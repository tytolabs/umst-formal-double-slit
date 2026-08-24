(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AuExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Au Z=79 d-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X79) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Au 5d10 6s1 d-block Madelung exception; Ag Z=47 / Cu Z=29 homolog not Au copy. *)
(*  auExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **au_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive AuExceptionContinuumModality : Type :=
  | au_exception_continuum_unwired
  | au_exception_continuum_assumed
  | au_exception_continuum_proved
  | au_exception_continuum_surrogate.

Definition auExceptionContinuumModalityCurrent :
  AuExceptionContinuumModality :=
  au_exception_continuum_unwired.

Definition au_exception_continuum_lattice_cardinality : nat := 4.

Lemma au_exception_continuum_lattice_cardinality_is_four :
  au_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma au_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb au_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold au_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — au_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_au_exception_continuum_idx : nat := 14.

Lemma pattern_class_au_exception_continuum_idx_is_14 :
  pattern_class_au_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma au_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_au_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_au_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X79".

Lemma cross_classifier_au_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X79".
Proof. reflexivity. Qed.

Definition pattern_class_au_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_au_exception_continuum_tag : string :=
  "X79 occupancy engine sort".

Lemma pattern_class_au_exception_continuum_tag_nonempty :
  pattern_class_au_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_au_exception_continuum_tag_nonempty :
  north_star_class_14_au_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Au Z=79 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition gold_atomic_number_z : nat := 79.

Lemma gold_atomic_number_z_is_79 :
  gold_atomic_number_z = 79.
Proof. reflexivity. Qed.

Definition gold_z_valid : bool :=
  Nat.ltb 0 gold_atomic_number_z &&
  Nat.leb gold_atomic_number_z iupac_table_cardinality.

Lemma gold_z_valid_true : gold_z_valid = true.
Proof.
  unfold gold_z_valid, gold_atomic_number_z, iupac_table_cardinality.
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

Definition au_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma au_exception_continuum_factor_tag_nonempty :
  au_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive auec_channel_slot : Type :=
  | auec_slot_unwired
  | auec_slot_absent
  | auec_slot_present.

Definition auec_channel_slot_beq (s1 s2 : auec_channel_slot) : bool :=
  match s1, s2 with
  | auec_slot_unwired, auec_slot_unwired => true
  | auec_slot_absent, auec_slot_absent => true
  | auec_slot_present, auec_slot_present => true
  | _, _ => false
  end.

Definition auec_channel_slot_is_present (s : auec_channel_slot) : bool :=
  match s with
  | auec_slot_present => true
  | _ => false
  end.

Definition auExceptionContinuumProductChannelCount : nat := 3.

Lemma au_exception_continuum_product_channel_count_is_three :
  auExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 au_exception_continuum. *)
Definition auec_channel_occupancy_engine_sort : nat := 0.
Definition auec_channel_observed_override : nat := 1.
Definition auec_channel_dblock_exception_continuum : nat := 2.

Lemma auec_channel_occupancy_engine_sort_idx_is_0 :
  auec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma auec_channel_observed_override_idx_is_1 :
  auec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma auec_channel_class9_au_exception_continuum_idx_is_2 :
  auec_channel_dblock_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition auec_channel_bundle : Type := nat -> auec_channel_slot.

Definition auExceptionContinuumBundleAllUnwired : auec_channel_bundle :=
  fun _ => auec_slot_unwired.

Definition auExceptionContinuumBundleAt (b : auec_channel_bundle) (idx : nat)
  (slot : auec_channel_slot) : auec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition auExceptionContinuumBundleWithPresent
  (b : auec_channel_bundle) (idx : nat) : auec_channel_bundle :=
  auExceptionContinuumBundleAt b idx auec_slot_present.

Fixpoint count_auec_present_up_to (b : auec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if auec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_auec_present_up_to b i + add
  end.

Definition auExceptionContinuumBundlePresentCount (b : auec_channel_bundle) : nat :=
  count_auec_present_up_to b auExceptionContinuumProductChannelCount.

Definition auExceptionContinuumBundleHolds (b : auec_channel_bundle) (idx : nat) : bool :=
  auec_channel_slot_is_present (b idx).

Definition auExceptionContinuumBundleIsConcurrentProduct (b : auec_channel_bundle) : bool :=
  Nat.leb 2 (auExceptionContinuumBundlePresentCount b).

(* Au Z=79 interact restriction + G-min + class 14 au_exception_continuum concurrent witness. *)
Definition auExceptionContinuumAu79Witness : auec_channel_bundle :=
  auExceptionContinuumBundleWithPresent
    (auExceptionContinuumBundleWithPresent
      (auExceptionContinuumBundleWithPresent auExceptionContinuumBundleAllUnwired
        auec_channel_occupancy_engine_sort)
      auec_channel_observed_override)
    auec_channel_dblock_exception_continuum.

Definition auExceptionContinuumEmptyWitness : auec_channel_bundle :=
  auExceptionContinuumBundleAllUnwired.

Definition auExceptionContinuumSinglePresent : auec_channel_bundle :=
  auExceptionContinuumBundleWithPresent auExceptionContinuumBundleAllUnwired
    auec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  auExceptionContinuumBundleHolds auExceptionContinuumAu79Witness
    auec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  auExceptionContinuumBundleHolds auExceptionContinuumAu79Witness
    auec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_au_exception_continuum_channel_present :
  auExceptionContinuumBundleHolds auExceptionContinuumAu79Witness
    auec_channel_dblock_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma au79_witness_present_count_is_three :
  auExceptionContinuumBundlePresentCount auExceptionContinuumAu79Witness = 3.
Proof. reflexivity. Qed.

Lemma au79_witness_is_concurrent_product :
  auExceptionContinuumBundleIsConcurrentProduct auExceptionContinuumAu79Witness = true.
Proof.
  unfold auExceptionContinuumBundleIsConcurrentProduct.
  rewrite au79_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  auExceptionContinuumBundlePresentCount auExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  auExceptionContinuumBundleIsConcurrentProduct auExceptionContinuumEmptyWitness = false.
Proof.
  unfold auExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  auExceptionContinuumBundlePresentCount auExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  auExceptionContinuumBundleIsConcurrentProduct auExceptionContinuumSinglePresent = false.
Proof.
  unfold auExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive auec_xor_posture : Type :=
  | auec_xor_exclusive
  | auec_xor_concurrent_product.

Definition auecXorClassifierMarker : string := "chem_l0_au_exception_continuum_xor_classifier_v1".
Definition auecConcurrentProductMarker : string := "chem_int_au_exception_continuum_product_v1".

Lemma auec_xor_marker_ne_concurrent_product_marker :
  auecXorClassifierMarker <> auecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition auecXorClassifierIncompatible (claim_xor : bool)
  (b : auec_channel_bundle) : bool :=
  claim_xor && auExceptionContinuumBundleIsConcurrentProduct b.

Lemma auec_xor_refuse_on_au79_witness :
  auecXorClassifierIncompatible true auExceptionContinuumAu79Witness = true.
Proof.
  unfold auecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma auec_xor_ok_on_concurrent_product_claim :
  auecXorClassifierIncompatible false auExceptionContinuumAu79Witness = false.
Proof. reflexivity. Qed.

Definition auecProductNotXor : bool :=
  auExceptionContinuumBundleIsConcurrentProduct auExceptionContinuumAu79Witness &&
  auecXorClassifierIncompatible true auExceptionContinuumAu79Witness.

Lemma auec_product_not_xor_true : auecProductNotXor = true.
Proof.
  unfold auecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  auecProductNotXor = true /\
  Nat.leb 2 (auExceptionContinuumBundlePresentCount
    auExceptionContinuumAu79Witness) = true /\
  auecXorClassifierMarker <> auecConcurrentProductMarker.
Proof.
  split.
  - apply auec_product_not_xor_true.
  - split.
    + rewrite au79_witness_present_count_is_three.
      reflexivity.
    + apply auec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive auec_bar_presence : Type :=
  | auec_bar_absent
  | auec_bar_present.

Record auec_claim_bar : Type := {
  auec_bar_presence_field : auec_bar_presence;
  auec_bar_defect_total : nat
}.

Definition auExceptionContinuumClaimBarAbsent : auec_claim_bar :=
  {| auec_bar_presence_field := auec_bar_absent;
     auec_bar_defect_total := 0 |}.

Definition auExceptionContinuumClaimBarZeroDefect : auec_claim_bar :=
  {| auec_bar_presence_field := auec_bar_present;
     auec_bar_defect_total := 0 |}.

Definition auec_claim_bar_zero_defect (b : auec_claim_bar) : bool :=
  match auec_bar_presence_field b with
  | auec_bar_absent => false
  | auec_bar_present => Nat.eqb (auec_bar_defect_total b) 0
  end.

Lemma auec_claim_bar_zero_defect_true :
  auec_claim_bar_zero_defect auExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma auec_claim_bar_absent_not_zero_defect :
  auec_claim_bar_zero_defect auExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive auec_conservation_verdict : Type :=
  | auec_verdict_unwired_ok
  | auec_verdict_named_ok
  | auec_verdict_design_ok
  | auec_verdict_trivial_refuse
  | auec_verdict_xor_refuse
  | auec_verdict_green_invent_refuse
  | auec_verdict_proved_without_bar_refuse
  | auec_verdict_production_wired_refuse
  | auec_verdict_parallel_au_exception_continuum_axiom_refuse
  | auec_verdict_species_id_smuggle_refuse
  | auec_verdict_extra_element_id_refuse
  | auec_verdict_extra_au_exception_continuum_force_refuse
  | auec_verdict_tp_float_pin_refuse.

Definition auec_conservation_verdict_ok (v : auec_conservation_verdict) : bool :=
  match v with
  | auec_verdict_unwired_ok => true
  | auec_verdict_named_ok => true
  | auec_verdict_design_ok => true
  | _ => false
  end.

Definition auExceptionContinuumBundleNontrivial (b : auec_channel_bundle) : bool :=
  Nat.ltb 0 (auExceptionContinuumBundlePresentCount b).

Definition evaluate_au_exception_continuum_bundle
  (m : AuExceptionContinuumModality)
  (b : auec_channel_bundle)
  (bar : auec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : auec_conservation_verdict :=
  if claim_physics_green
  then auec_verdict_green_invent_refuse
  else if claim_proved
       then auec_verdict_proved_without_bar_refuse
       else if negb (auExceptionContinuumBundleNontrivial b)
            then auec_verdict_trivial_refuse
            else if auecXorClassifierIncompatible claim_xor_classifier b
                 then auec_verdict_xor_refuse
                 else
                   match m with
                   | au_exception_continuum_unwired =>
                       if auExceptionContinuumBundleIsConcurrentProduct b
                       then auec_verdict_named_ok
                       else auec_verdict_design_ok
                   | au_exception_continuum_assumed
                   | au_exception_continuum_surrogate =>
                       auec_verdict_design_ok
                   | au_exception_continuum_proved =>
                       auec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_au_exception_continuum_close
  (m : AuExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : auec_conservation_verdict :=
  if claim_physics_green
  then auec_verdict_green_invent_refuse
  else if claim_production_wired
  then auec_verdict_production_wired_refuse
  else
    match m with
    | au_exception_continuum_unwired => auec_verdict_unwired_ok
    | au_exception_continuum_assumed
    | au_exception_continuum_proved
    | au_exception_continuum_surrogate => auec_verdict_named_ok
    end.

Definition au_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_au_exception_continuum_close
          au_exception_continuum_proved claim_physics_green claim_production_wired with
  | auec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive auec_conservation_law : Type :=
  | auec_law_conserved
  | auec_law_named_ok
  | auec_law_trivial_refuse
  | auec_law_green_invent_refuse.

Definition auec_conservation_law_count : nat := 4.

Lemma auec_conservation_law_count_is_four :
  auec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive auec_conservation_law_witness : Type :=
  | auec_law_witness_open
  | auec_law_witness_proved.

Definition evaluate_auec_conservation_law_witness
  (law : auec_conservation_law)
  (m : AuExceptionContinuumModality)
  : auec_conservation_law_witness :=
  match m with
  | au_exception_continuum_unwired
  | au_exception_continuum_assumed
  | au_exception_continuum_surrogate => auec_law_witness_open
  | au_exception_continuum_proved => auec_law_witness_proved
  end.

Lemma all_auec_conservation_laws_open_at_unwired :
  evaluate_auec_conservation_law_witness auec_law_conserved
    au_exception_continuum_unwired = auec_law_witness_open /\
  evaluate_auec_conservation_law_witness auec_law_named_ok
    au_exception_continuum_unwired = auec_law_witness_open /\
  evaluate_auec_conservation_law_witness auec_law_trivial_refuse
    au_exception_continuum_unwired = auec_law_witness_open /\
  evaluate_auec_conservation_law_witness auec_law_green_invent_refuse
    au_exception_continuum_unwired = auec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition auExceptionContinuumProved : bool := false.

Lemma au_exception_continuum_proved_false :
  auExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_au_exception_continuum_close
    au_exception_continuum_unwired false false =
  auec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_au_exception_continuum_close
    au_exception_continuum_unwired false false =
  auec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_unwired false false) =
  true.
Proof.
  unfold auec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Au Z=79 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma au79_witness_named_ok :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false false =
  auec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_au79_au_exception_continuum :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false false =
  auec_verdict_named_ok /\
  auExceptionContinuumBundleIsConcurrentProduct auExceptionContinuumAu79Witness = true /\
  gold_atomic_number_z = 79 /\
  pattern_class_au_exception_continuum_idx = 14.
Proof.
  repeat split; reflexivity.
Qed.

Lemma auec_named_close_ok :
  evaluate_au_exception_continuum_close
    au_exception_continuum_proved false false =
  auec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_au_exception_continuum_close :
  evaluate_au_exception_continuum_close
    au_exception_continuum_proved false false =
  auec_verdict_named_ok /\
  au_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply auec_named_close_ok.
  - unfold au_exception_continuum_authorized.
    rewrite auec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — au_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumEmptyWitness
    auExceptionContinuumClaimBarAbsent false false false =
  auec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumEmptyWitness
    auExceptionContinuumClaimBarAbsent false false false =
  auec_verdict_trivial_refuse /\
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_bundle
       au_exception_continuum_unwired
       auExceptionContinuumEmptyWitness
       auExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold auec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent true false false =
  auec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent true false false =
  auec_verdict_xor_refuse /\
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_bundle
       au_exception_continuum_unwired
       auExceptionContinuumAu79Witness
       auExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold auec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_au_exception_continuum_close
    au_exception_continuum_unwired true false =
  auec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_unwired true false) =
  false.
Proof.
  unfold auec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_auec_bundle_refuse :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false true false =
  auec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — au_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false true =
  auec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false true =
  auec_verdict_proved_without_bar_refuse /\
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_bundle
       au_exception_continuum_unwired
       auExceptionContinuumAu79Witness
       auExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold auec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — au_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_au_exception_continuum_close
    au_exception_continuum_proved false true =
  auec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_proved false true) =
  false.
Proof.
  unfold auec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel au_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition auExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelAuExceptionAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_au_exception_continuum_axiom_refuse :
  auExceptionContinuumAuthority <>
  parallelAuExceptionAxiomTag /\
  auExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply au_exception_continuum_proved_false.
Qed.

Theorem parallel_au_exception_continuum_axiom_not_minted :
  auExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  auExceptionContinuumProved = false /\
  auExceptionContinuumAuthority <> parallelAuExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopySmuggleFraming : string :=
  "homolog_subshell_copy_not_named_object".

Definition auExceptionContinuumFraming : string :=
  "second_law_conservation_au_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  auExceptionContinuumFraming <>
  homologCopySmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_au_exception_continuum_idx = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem occupancy_engine_sort_not_homolog_copy_smuggle :
  auExceptionContinuumFraming <>
  homologCopySmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_au_exception_continuum_idx = 14 /\
  auExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — au_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "homolog_occupancy_subshell_copy_smuggle".

Lemma extra_element_id_refuse :
  auExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  auExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — au_exception_continuum ≠ extra au_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_au_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/au_exception_continuum_barrier.rs".

Lemma extra_au_exception_continuum_force_refuse :
  auExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem au_exception_continuum_not_extra_au_exception_continuum_force :
  auExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/au_exception_continuum_barrier.rs" /\
  auExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_au_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  auExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  auExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  AuExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition auec_conservation_coherence_scaffold : bool :=
  auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_proved false false) &&
  negb (auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_unwired true false)) &&
  negb (auec_conservation_verdict_ok
    (evaluate_au_exception_continuum_close
       au_exception_continuum_proved false true)).

Lemma auec_conservation_coherence_scaffold_true :
  auec_conservation_coherence_scaffold = true.
Proof.
  unfold auec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem auec_conservation_coherence_scaffold_theorem :
  evaluate_au_exception_continuum_close
    au_exception_continuum_proved false false =
    auec_verdict_named_ok /\
  evaluate_au_exception_continuum_close
    au_exception_continuum_unwired true false =
    auec_verdict_green_invent_refuse /\
  evaluate_au_exception_continuum_close
    au_exception_continuum_proved false true =
    auec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition auec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition auec_conservation_knowing_fiber_ok : bool :=
  auec_conservation_fiber_ok fiber_quantum_knowing.

Definition auec_conservation_meso_acting_ok : bool :=
  auec_conservation_fiber_ok fiber_meso_acting.

Lemma auec_conservation_knowing_fiber_ok_true :
  auec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma auec_conservation_meso_acting_not_ok :
  auec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem auec_conservation_routes_knowing_not_meso :
  auec_conservation_knowing_fiber_ok = true /\
  auec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply auec_conservation_knowing_fiber_ok_true.
  - apply auec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  auec_conservation_knowing_fiber_ok &&
  negb auec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, auec_conservation_knowing_fiber_ok,
    auec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem au_exception_continuum_fixture_scaffold :
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false false =
    auec_verdict_named_ok /\
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumEmptyWitness
    auExceptionContinuumClaimBarAbsent false false false =
    auec_verdict_trivial_refuse /\
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent true false false =
    auec_verdict_xor_refuse /\
  evaluate_au_exception_continuum_bundle
    au_exception_continuum_unwired
    auExceptionContinuumAu79Witness
    auExceptionContinuumClaimBarAbsent false false true =
    auec_verdict_proved_without_bar_refuse /\
  evaluate_au_exception_continuum_close
    au_exception_continuum_unwired false false =
    auec_verdict_unwired_ok /\
  auec_conservation_knowing_fiber_ok = true /\
  auec_conservation_meso_acting_ok = false /\
  auExceptionContinuumProved = false /\
  auecProductNotXor = true /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ag Z=47 / Cu Z=29 homolog not Au copy — group-11 homolog ≠ identity *)
(* ------------------------------------------------------------------ *)

Definition silver_atomic_number_z : nat := 47.

Lemma silver_atomic_number_z_is_47 :
  silver_atomic_number_z = 47.
Proof. reflexivity. Qed.

Definition copper_atomic_number_z : nat := 29.

Lemma copper_atomic_number_z_is_29 :
  copper_atomic_number_z = 29.
Proof. reflexivity. Qed.

Definition gold_occupancy_tag : string := "5d106s1".

Definition silver_occupancy_tag : string := "4d105s1".

Definition copper_occupancy_tag : string := "3d104s1".

Lemma gold_silver_occupancy_tags_distinct :
  gold_occupancy_tag <> silver_occupancy_tag.
Proof. discriminate. Qed.

Lemma gold_copper_occupancy_tags_distinct :
  gold_occupancy_tag <> copper_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma ag_au_homolog_not_copy :
  gold_atomic_number_z = 79 /\
  silver_atomic_number_z = 47 /\
  gold_occupancy_tag <> silver_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Lemma cu_au_homolog_not_copy :
  gold_atomic_number_z = 79 /\
  copper_atomic_number_z = 29 /\
  gold_occupancy_tag <> copper_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ag_cu_homolog_not_au_occupancy_copy :
  gold_atomic_number_z = 79 /\
  silver_atomic_number_z = 47 /\
  copper_atomic_number_z = 29 /\
  gold_occupancy_tag = "5d106s1" /\
  silver_occupancy_tag = "4d105s1" /\
  copper_occupancy_tag = "3d104s1" /\
  gold_occupancy_tag <> silver_occupancy_tag /\
  gold_occupancy_tag <> copper_occupancy_tag /\
  auExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — au_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition auExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition auExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-AU-EXCEPTION-CONTINUUM".

Definition auExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-AU-EXCEPTION-CONTINUUM AuExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice auExceptionContinuumProved false evaluateAuExceptionContinuumBundle evaluateAuExceptionContinuum named Au Z=79 d-block occupancy exception continuum X79 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel au exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ag Z=47 Cu Z=29 homolog not Au 5d10 6s1 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma au_exception_continuum_cell_id :
  auExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-AU-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma au_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma au_exception_continuum_authority_path :
  auExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma au_exception_continuum_cites_l0_ore02 :
  auExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma au_exception_continuum_cites_marker :
  auecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma au_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma au_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma au_exception_continuum_not_26th_axiom :
  auExceptionContinuumFraming <> parallelAuExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma au_exception_continuum_second_law_conservation_framing :
  auExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_au_exception_continuum_morphism".

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
  auExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not au_exception_continuum axiom / extra force     *)
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

Theorem au_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/au_exception_continuum_barrier.rs" /\
  auExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma au_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma au_exception_continuum_modality_unwired :
  auExceptionContinuumModalityCurrent =
  au_exception_continuum_unwired.
Proof. reflexivity. Qed.

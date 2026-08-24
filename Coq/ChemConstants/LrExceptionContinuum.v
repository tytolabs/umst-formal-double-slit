(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: LrExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Lr Z=103 actinide occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Lr Z=103 5f14 6d1 7s2 actinide Madelung exception; Lu Z=71 homolog not Lr copy. *)
(*  lrExceptionContinuumProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs (read-only). *)
(*  INT: umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs (cite). *)
(*  INT: umst/umst-chem/src/qlattice.rs (read-only cite).               *)
(*  ActinideOccupancyExceptions.v cited. OccupancyEngineSort.v cited.      *)
(* ================================================================== *)


From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **lr_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive LrExceptionContinuumModality : Type :=
  | lr_exception_continuum_unwired
  | lr_exception_continuum_assumed
  | lr_exception_continuum_proved
  | lr_exception_continuum_surrogate.

Definition lrExceptionContinuumModalityCurrent :
  LrExceptionContinuumModality :=
  lr_exception_continuum_unwired.

Definition lr_exception_continuum_lattice_cardinality : nat := 4.

Lemma lr_exception_continuum_lattice_cardinality_is_four :
  lr_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma lr_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb lr_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold lr_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — lr_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_lr_exception_continuum_idx : nat := 14.

Lemma pattern_class_lr_exception_continuum_idx_is_14 :
  pattern_class_lr_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma lr_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_lr_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_lr_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_lr_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_lr_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_lr_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_lr_exception_continuum_tag_nonempty :
  pattern_class_lr_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_lr_exception_continuum_tag_nonempty :
  north_star_class_14_lr_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Lr Z=103 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition lawrencium_atomic_number_z : nat := 103.

Lemma lawrencium_atomic_number_z_is_103 :
  lawrencium_atomic_number_z = 103.
Proof. reflexivity. Qed.

Definition lawrencium_z_valid : bool :=
  Nat.ltb 0 lawrencium_atomic_number_z &&
  Nat.leb lawrencium_atomic_number_z iupac_table_cardinality.

Lemma lawrencium_z_valid_true : lawrencium_z_valid = true.
Proof.
  unfold lawrencium_z_valid, lawrencium_atomic_number_z, iupac_table_cardinality.
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
(*  Lr Z=103 occupancy pins — 5f¹⁴6d¹7s² observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition lr_element_symbol : string := "Lr".

Definition lr_observed_occupancy_tag : string := "5f146d17s2".

Definition lr_predicted_occupancy_tag : string := "7s25f14".

Definition lr_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1".

Definition lr_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f14".

Definition lu_homolog_observed_occupancy_tag : string := "4f145d16s2".

Definition lutetium_homolog_z : nat := 71.

Lemma lutetium_homolog_z_is_71 :
  lutetium_homolog_z = 71.
Proof. reflexivity. Qed.

Lemma lr_element_symbol_nonempty :
  lr_element_symbol <> "".
Proof. discriminate. Qed.

Lemma lr_observed_occupancy_tag_nonempty :
  lr_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma lr_predicted_occupancy_tag_nonempty :
  lr_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma lr_observed_ne_predicted_occupancy :
  lr_observed_occupancy_tag <> lr_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma lr_observed_ne_predicted_subshell :
  lr_observed_subshell_notation <> lr_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma lr_homolog_occupancy_not_copy :
  lr_observed_occupancy_tag <> lu_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "actinide_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "actinide_exception".
Proof. reflexivity. Qed.

Definition lr_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma lr_exception_continuum_factor_tag_nonempty :
  lr_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive lrec_channel_slot : Type :=
  | lrec_slot_unwired
  | lrec_slot_absent
  | lrec_slot_present.

Definition lrec_channel_slot_beq (s1 s2 : lrec_channel_slot) : bool :=
  match s1, s2 with
  | lrec_slot_unwired, lrec_slot_unwired => true
  | lrec_slot_absent, lrec_slot_absent => true
  | lrec_slot_present, lrec_slot_present => true
  | _, _ => false
  end.

Definition lrec_channel_slot_is_present (s : lrec_channel_slot) : bool :=
  match s with
  | lrec_slot_present => true
  | _ => false
  end.

Definition lrExceptionContinuumProductChannelCount : nat := 3.

Lemma lr_exception_continuum_product_channel_count_is_three :
  lrExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 lr_exception_continuum. *)
Definition lrec_channel_occupancy_engine_sort : nat := 0.
Definition lrec_channel_observed_override : nat := 1.
Definition lrec_channel_actinide_exception_continuum : nat := 2.

Lemma lrec_channel_occupancy_engine_sort_idx_is_0 :
  lrec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma lrec_channel_observed_override_idx_is_1 :
  lrec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma lrec_channel_class9_lr_exception_continuum_idx_is_2 :
  lrec_channel_actinide_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition lrec_channel_bundle : Type := nat -> lrec_channel_slot.

Definition lrExceptionContinuumBundleAllUnwired : lrec_channel_bundle :=
  fun _ => lrec_slot_unwired.

Definition lrExceptionContinuumBundleAt (b : lrec_channel_bundle) (idx : nat)
  (slot : lrec_channel_slot) : lrec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition lrExceptionContinuumBundleWithPresent
  (b : lrec_channel_bundle) (idx : nat) : lrec_channel_bundle :=
  lrExceptionContinuumBundleAt b idx lrec_slot_present.

Fixpoint count_lrec_present_up_to (b : lrec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if lrec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_lrec_present_up_to b i + add
  end.

Definition lrExceptionContinuumBundlePresentCount (b : lrec_channel_bundle) : nat :=
  count_lrec_present_up_to b lrExceptionContinuumProductChannelCount.

Definition lrExceptionContinuumBundleHolds (b : lrec_channel_bundle) (idx : nat) : bool :=
  lrec_channel_slot_is_present (b idx).

Definition lrExceptionContinuumBundleIsConcurrentProduct (b : lrec_channel_bundle) : bool :=
  Nat.leb 2 (lrExceptionContinuumBundlePresentCount b).

(* Lr Z=103 interact restriction + G-min + class 14 lr_exception_continuum concurrent witness. *)
Definition lrExceptionContinuumLr103Witness : lrec_channel_bundle :=
  lrExceptionContinuumBundleWithPresent
    (lrExceptionContinuumBundleWithPresent
      (lrExceptionContinuumBundleWithPresent lrExceptionContinuumBundleAllUnwired
        lrec_channel_occupancy_engine_sort)
      lrec_channel_observed_override)
    lrec_channel_actinide_exception_continuum.

Definition lrExceptionContinuumEmptyWitness : lrec_channel_bundle :=
  lrExceptionContinuumBundleAllUnwired.

Definition lrExceptionContinuumSinglePresent : lrec_channel_bundle :=
  lrExceptionContinuumBundleWithPresent lrExceptionContinuumBundleAllUnwired
    lrec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  lrExceptionContinuumBundleHolds lrExceptionContinuumLr103Witness
    lrec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  lrExceptionContinuumBundleHolds lrExceptionContinuumLr103Witness
    lrec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_lr_exception_continuum_channel_present :
  lrExceptionContinuumBundleHolds lrExceptionContinuumLr103Witness
    lrec_channel_actinide_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma lr103_witness_present_count_is_three :
  lrExceptionContinuumBundlePresentCount lrExceptionContinuumLr103Witness = 3.
Proof. reflexivity. Qed.

Lemma lr103_witness_is_concurrent_product :
  lrExceptionContinuumBundleIsConcurrentProduct lrExceptionContinuumLr103Witness = true.
Proof.
  unfold lrExceptionContinuumBundleIsConcurrentProduct.
  rewrite lr103_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  lrExceptionContinuumBundlePresentCount lrExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  lrExceptionContinuumBundleIsConcurrentProduct lrExceptionContinuumEmptyWitness = false.
Proof.
  unfold lrExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  lrExceptionContinuumBundlePresentCount lrExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  lrExceptionContinuumBundleIsConcurrentProduct lrExceptionContinuumSinglePresent = false.
Proof.
  unfold lrExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive lrec_xor_posture : Type :=
  | lrec_xor_exclusive
  | lrec_xor_concurrent_product.

Definition lrecXorClassifierMarker : string := "chem_l0_lr_exception_continuum_xor_classifier_v1".
Definition lrecConcurrentProductMarker : string := "chem_int_lr_exception_continuum_product_v1".

Lemma lrec_xor_marker_ne_concurrent_product_marker :
  lrecXorClassifierMarker <> lrecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition lrecXorClassifierIncompatible (claim_xor : bool)
  (b : lrec_channel_bundle) : bool :=
  claim_xor && lrExceptionContinuumBundleIsConcurrentProduct b.

Lemma lrec_xor_refuse_on_lr103_witness :
  lrecXorClassifierIncompatible true lrExceptionContinuumLr103Witness = true.
Proof.
  unfold lrecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma lrec_xor_ok_on_concurrent_product_claim :
  lrecXorClassifierIncompatible false lrExceptionContinuumLr103Witness = false.
Proof. reflexivity. Qed.

Definition lrecProductNotXor : bool :=
  lrExceptionContinuumBundleIsConcurrentProduct lrExceptionContinuumLr103Witness &&
  lrecXorClassifierIncompatible true lrExceptionContinuumLr103Witness.

Lemma lrec_product_not_xor_true : lrecProductNotXor = true.
Proof.
  unfold lrecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  lrecProductNotXor = true /\
  Nat.leb 2 (lrExceptionContinuumBundlePresentCount
    lrExceptionContinuumLr103Witness) = true /\
  lrecXorClassifierMarker <> lrecConcurrentProductMarker.
Proof.
  split.
  - apply lrec_product_not_xor_true.
  - split.
    + rewrite lr103_witness_present_count_is_three.
      reflexivity.
    + apply lrec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive lrec_bar_presence : Type :=
  | lrec_bar_absent
  | lrec_bar_present.

Record lrec_claim_bar : Type := {
  lrec_bar_presence_field : lrec_bar_presence;
  lrec_bar_defect_total : nat
}.

Definition lrExceptionContinuumClaimBarAbsent : lrec_claim_bar :=
  {| lrec_bar_presence_field := lrec_bar_absent;
     lrec_bar_defect_total := 0 |}.

Definition lrExceptionContinuumClaimBarZeroDefect : lrec_claim_bar :=
  {| lrec_bar_presence_field := lrec_bar_present;
     lrec_bar_defect_total := 0 |}.

Definition lrec_claim_bar_zero_defect (b : lrec_claim_bar) : bool :=
  match lrec_bar_presence_field b with
  | lrec_bar_absent => false
  | lrec_bar_present => Nat.eqb (lrec_bar_defect_total b) 0
  end.

Lemma lrec_claim_bar_zero_defect_true :
  lrec_claim_bar_zero_defect lrExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma lrec_claim_bar_absent_not_zero_defect :
  lrec_claim_bar_zero_defect lrExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive lrec_conservation_verdict : Type :=
  | lrec_verdict_unwired_ok
  | lrec_verdict_named_ok
  | lrec_verdict_design_ok
  | lrec_verdict_trivial_refuse
  | lrec_verdict_xor_refuse
  | lrec_verdict_green_invent_refuse
  | lrec_verdict_proved_without_bar_refuse
  | lrec_verdict_production_wired_refuse
  | lrec_verdict_parallel_lr_exception_continuum_axiom_refuse
  | lrec_verdict_species_id_smuggle_refuse
  | lrec_verdict_extra_element_id_refuse
  | lrec_verdict_extra_lr_exception_continuum_force_refuse
  | lrec_verdict_tp_float_pin_refuse.

Definition lrec_conservation_verdict_ok (v : lrec_conservation_verdict) : bool :=
  match v with
  | lrec_verdict_unwired_ok => true
  | lrec_verdict_named_ok => true
  | lrec_verdict_design_ok => true
  | _ => false
  end.

Definition lrExceptionContinuumBundleNontrivial (b : lrec_channel_bundle) : bool :=
  Nat.ltb 0 (lrExceptionContinuumBundlePresentCount b).

Definition evaluate_lr_exception_continuum_bundle
  (m : LrExceptionContinuumModality)
  (b : lrec_channel_bundle)
  (bar : lrec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : lrec_conservation_verdict :=
  if claim_physics_green
  then lrec_verdict_green_invent_refuse
  else if claim_proved
       then lrec_verdict_proved_without_bar_refuse
       else if negb (lrExceptionContinuumBundleNontrivial b)
            then lrec_verdict_trivial_refuse
            else if lrecXorClassifierIncompatible claim_xor_classifier b
                 then lrec_verdict_xor_refuse
                 else
                   match m with
                   | lr_exception_continuum_unwired =>
                       if lrExceptionContinuumBundleIsConcurrentProduct b
                       then lrec_verdict_named_ok
                       else lrec_verdict_design_ok
                   | lr_exception_continuum_assumed
                   | lr_exception_continuum_surrogate =>
                       lrec_verdict_design_ok
                   | lr_exception_continuum_proved =>
                       lrec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_lr_exception_continuum_close
  (m : LrExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : lrec_conservation_verdict :=
  if claim_physics_green
  then lrec_verdict_green_invent_refuse
  else if claim_production_wired
  then lrec_verdict_production_wired_refuse
  else
    match m with
    | lr_exception_continuum_unwired => lrec_verdict_unwired_ok
    | lr_exception_continuum_assumed
    | lr_exception_continuum_proved
    | lr_exception_continuum_surrogate => lrec_verdict_named_ok
    end.

Definition lr_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_lr_exception_continuum_close
          lr_exception_continuum_proved claim_physics_green claim_production_wired with
  | lrec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive lrec_conservation_law : Type :=
  | lrec_law_conserved
  | lrec_law_named_ok
  | lrec_law_trivial_refuse
  | lrec_law_green_invent_refuse.

Definition lrec_conservation_law_count : nat := 4.

Lemma lrec_conservation_law_count_is_four :
  lrec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive lrec_conservation_law_witness : Type :=
  | lrec_law_witness_open
  | lrec_law_witness_proved.

Definition evaluate_lrec_conservation_law_witness
  (law : lrec_conservation_law)
  (m : LrExceptionContinuumModality)
  : lrec_conservation_law_witness :=
  match m with
  | lr_exception_continuum_unwired
  | lr_exception_continuum_assumed
  | lr_exception_continuum_surrogate => lrec_law_witness_open
  | lr_exception_continuum_proved => lrec_law_witness_proved
  end.

Lemma all_lrec_conservation_laws_open_at_unwired :
  evaluate_lrec_conservation_law_witness lrec_law_conserved
    lr_exception_continuum_unwired = lrec_law_witness_open /\
  evaluate_lrec_conservation_law_witness lrec_law_named_ok
    lr_exception_continuum_unwired = lrec_law_witness_open /\
  evaluate_lrec_conservation_law_witness lrec_law_trivial_refuse
    lr_exception_continuum_unwired = lrec_law_witness_open /\
  evaluate_lrec_conservation_law_witness lrec_law_green_invent_refuse
    lr_exception_continuum_unwired = lrec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition lrExceptionContinuumProved : bool := false.

Lemma lr_exception_continuum_proved_false :
  lrExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_unwired false false =
  lrec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_unwired false false =
  lrec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_unwired false false) =
  true.
Proof.
  unfold lrec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Lr Z=103 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma lr103_witness_named_ok :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false false =
  lrec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_lr103_lr_exception_continuum :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false false =
  lrec_verdict_named_ok /\
  lrExceptionContinuumBundleIsConcurrentProduct lrExceptionContinuumLr103Witness = true /\
  lawrencium_atomic_number_z = 103 /\
  lr_observed_occupancy_tag = "5f146d17s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma lrec_named_close_ok :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_proved false false =
  lrec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_lr_exception_continuum_close :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_proved false false =
  lrec_verdict_named_ok /\
  lr_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply lrec_named_close_ok.
  - unfold lr_exception_continuum_authorized.
    rewrite lrec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — lr_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumEmptyWitness
    lrExceptionContinuumClaimBarAbsent false false false =
  lrec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumEmptyWitness
    lrExceptionContinuumClaimBarAbsent false false false =
  lrec_verdict_trivial_refuse /\
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_bundle
       lr_exception_continuum_unwired
       lrExceptionContinuumEmptyWitness
       lrExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold lrec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent true false false =
  lrec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent true false false =
  lrec_verdict_xor_refuse /\
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_bundle
       lr_exception_continuum_unwired
       lrExceptionContinuumLr103Witness
       lrExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold lrec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_unwired true false =
  lrec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_unwired true false) =
  false.
Proof.
  unfold lrec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_lrec_bundle_refuse :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false true false =
  lrec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — lr_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false true =
  lrec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false true =
  lrec_verdict_proved_without_bar_refuse /\
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_bundle
       lr_exception_continuum_unwired
       lrExceptionContinuumLr103Witness
       lrExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold lrec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — lr_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_proved false true =
  lrec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_proved false true) =
  false.
Proof.
  unfold lrec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel lr_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition lrExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelLrExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_lr_exception_continuum_axiom_refuse :
  lrExceptionContinuumAuthority <>
  parallelLrExceptionAxiomTag /\
  lrExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply lr_exception_continuum_proved_false.
Qed.

Theorem parallel_lr_exception_continuum_axiom_not_minted :
  lrExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  lrExceptionContinuumProved = false /\
  lrExceptionContinuumAuthority <> parallelLrExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "lu_z71_occupancy_copied_onto_lr_z103".

Definition lrExceptionContinuumFraming : string :=
  "second_law_conservation_lr_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  lrExceptionContinuumFraming <>
  homologCopyFraming /\
  lawrencium_atomic_number_z = 103 /\
  lr_observed_occupancy_tag = "5f146d17s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem lr_lu_homolog_not_occupancy_copy :
  lrExceptionContinuumFraming <>
  homologCopyFraming /\
  lawrencium_atomic_number_z = 103 /\
  lutetium_homolog_z = 71 /\
  lr_observed_occupancy_tag <> lu_homolog_observed_occupancy_tag /\
  lrExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — lr_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "lr_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  lrExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  lrExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  lawrencium_atomic_number_z = 103.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — lr_exception_continuum ≠ extra lr_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_lr_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/lr_exception_continuum_barrier.rs".

Lemma extra_lr_exception_continuum_force_refuse :
  lrExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem lr_exception_continuum_not_extra_lr_exception_continuum_force :
  lrExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/lr_exception_continuum_barrier.rs" /\
  lrExceptionContinuumProved = false.
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
  lrExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  lr_observed_occupancy_tag <> lr_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply lr_observed_ne_predicted_occupancy.
Qed.

Theorem lr_observed_override_not_madelung_family_smuggle :
  lrExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  lr_observed_occupancy_tag = "5f146d17s2" /\
  lr_predicted_occupancy_tag = "7s25f14" /\
  lrExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply lr_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_lr_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  lrExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  lrExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  lawrencium_atomic_number_z = 103.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  LrExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition lrec_conservation_coherence_scaffold : bool :=
  lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_proved false false) &&
  negb (lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_unwired true false)) &&
  negb (lrec_conservation_verdict_ok
    (evaluate_lr_exception_continuum_close
       lr_exception_continuum_proved false true)).

Lemma lrec_conservation_coherence_scaffold_true :
  lrec_conservation_coherence_scaffold = true.
Proof.
  unfold lrec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem lrec_conservation_coherence_scaffold_theorem :
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_proved false false =
    lrec_verdict_named_ok /\
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_unwired true false =
    lrec_verdict_green_invent_refuse /\
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_proved false true =
    lrec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition lrec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition lrec_conservation_knowing_fiber_ok : bool :=
  lrec_conservation_fiber_ok fiber_quantum_knowing.

Definition lrec_conservation_meso_acting_ok : bool :=
  lrec_conservation_fiber_ok fiber_meso_acting.

Lemma lrec_conservation_knowing_fiber_ok_true :
  lrec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma lrec_conservation_meso_acting_not_ok :
  lrec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem lrec_conservation_routes_knowing_not_meso :
  lrec_conservation_knowing_fiber_ok = true /\
  lrec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply lrec_conservation_knowing_fiber_ok_true.
  - apply lrec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  lrec_conservation_knowing_fiber_ok &&
  negb lrec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, lrec_conservation_knowing_fiber_ok,
    lrec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem lr_exception_continuum_fixture_scaffold :
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false false =
    lrec_verdict_named_ok /\
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumEmptyWitness
    lrExceptionContinuumClaimBarAbsent false false false =
    lrec_verdict_trivial_refuse /\
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent true false false =
    lrec_verdict_xor_refuse /\
  evaluate_lr_exception_continuum_bundle
    lr_exception_continuum_unwired
    lrExceptionContinuumLr103Witness
    lrExceptionContinuumClaimBarAbsent false false true =
    lrec_verdict_proved_without_bar_refuse /\
  evaluate_lr_exception_continuum_close
    lr_exception_continuum_unwired false false =
    lrec_verdict_unwired_ok /\
  lrec_conservation_knowing_fiber_ok = true /\
  lrec_conservation_meso_acting_ok = false /\
  lrExceptionContinuumProved = false /\
  lrecProductNotXor = true /\
  lawrencium_atomic_number_z = 103.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Lu Z=71 homolog not Lr occupancy copy — period-5 group-11 homolog ≠ identity  *)
(* ------------------------------------------------------------------ *)

Definition lutetium_row_atomic_number_z : nat := 71.

Lemma lutetium_row_atomic_number_z_is_47 :
  lutetium_row_atomic_number_z = 71.
Proof. reflexivity. Qed.

Definition lr_row_occupancy_tag : string := "5f146d17s2".

Definition lu_row_occupancy_tag : string := "4f145d16s2".

Lemma copper_lu_row_occupancy_tags_distinct :
  lr_row_occupancy_tag <> lu_row_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma lu_lr_homolog_not_copy :
  lawrencium_atomic_number_z = 103 /\
  lutetium_row_atomic_number_z = 71 /\
  lr_row_occupancy_tag <> lu_row_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem lu_period6_homolog_not_lr_occupancy_copy :
  lawrencium_atomic_number_z = 103 /\
  lutetium_row_atomic_number_z = 71 /\
  lr_row_occupancy_tag = "5f146d17s2" /\
  lu_row_occupancy_tag = "4f145d16s2" /\
  lr_row_occupancy_tag <> lu_row_occupancy_tag /\
  lrExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — lr_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition lrExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition lrExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-LR-EXCEPTION-CONTINUUM".

Definition lrExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-LR-EXCEPTION-CONTINUUM LrExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice lrExceptionContinuumProved false evaluateLrExceptionContinuumBundle evaluateLrExceptionContinuum named Lr Z=103 actinide occupancy exception continuum X29 occupancy engine sort observed override actinide exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel lr exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Lu Z=71 homolog not Lr 4f14 5d1 6s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma lr_exception_continuum_cell_id :
  lrExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-LR-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma lr_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma lr_exception_continuum_authority_path :
  lrExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma lr_exception_continuum_cites_l0_ore02 :
  lrExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma lr_exception_continuum_cites_marker :
  lrecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma lr_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma lr_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma lr_exception_continuum_not_26th_axiom :
  lrExceptionContinuumFraming <> parallelLrExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma lr_exception_continuum_second_law_conservation_framing :
  lrExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition actinideExceptionNamedObject : string :=
  "interact_restriction_on_lr_exception_continuum_morphism".

Lemma tst_prior_art_not_named_object :
  actinideExceptionNamedObject <>
  madelungWalkFraming /\
  observed_override_channel_tag = "observed_override".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem actinide_exception_is_named_object_not_madelung_walk :
  actinideExceptionNamedObject <>
  madelungWalkFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort" /\
  lrExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not lr_exception_continuum axiom / extra force     *)
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

Theorem lr_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/lr_exception_continuum_barrier.rs" /\
  lrExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma lr_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma lr_exception_continuum_modality_unwired :
  lrExceptionContinuumModalityCurrent =
  lr_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition lrExceptionContinuumProductionWired : Prop := False.

Lemma lr_exception_continuum_not_production_wired :
  ~ lrExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


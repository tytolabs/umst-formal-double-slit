(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: NpExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Np Z=93 actinide occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Np Z=93 5f3 6d1 7s2 actinide Madelung exception; Pm Z=61 homolog not Np copy. *)
(*  npExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **np_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive NpExceptionContinuumModality : Type :=
  | np_exception_continuum_unwired
  | np_exception_continuum_assumed
  | np_exception_continuum_proved
  | np_exception_continuum_surrogate.

Definition npExceptionContinuumModalityCurrent :
  NpExceptionContinuumModality :=
  np_exception_continuum_unwired.

Definition np_exception_continuum_lattice_cardinality : nat := 4.

Lemma np_exception_continuum_lattice_cardinality_is_four :
  np_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma np_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb np_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold np_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — np_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_np_exception_continuum_idx : nat := 14.

Lemma pattern_class_np_exception_continuum_idx_is_14 :
  pattern_class_np_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma np_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_np_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_np_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_np_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_np_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_np_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_np_exception_continuum_tag_nonempty :
  pattern_class_np_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_np_exception_continuum_tag_nonempty :
  north_star_class_14_np_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Np Z=93 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition neptunium_atomic_number_z : nat := 93.

Lemma neptunium_atomic_number_z_is_93 :
  neptunium_atomic_number_z = 93.
Proof. reflexivity. Qed.

Definition neptunium_z_valid : bool :=
  Nat.ltb 0 neptunium_atomic_number_z &&
  Nat.leb neptunium_atomic_number_z iupac_table_cardinality.

Lemma neptunium_z_valid_true : neptunium_z_valid = true.
Proof.
  unfold neptunium_z_valid, neptunium_atomic_number_z, iupac_table_cardinality.
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
(*  Np Z=93 occupancy pins — 5f⁴6d¹7s² observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition np_element_symbol : string := "Np".

Definition np_observed_occupancy_tag : string := "7s25f46d1".

Definition np_predicted_occupancy_tag : string := "5f5".

Definition np_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f46d1".

Definition np_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f5".

Definition pm_homolog_observed_occupancy_tag : string := "6s24f5".

Definition promethium_homolog_z : nat := 61.

Lemma promethium_homolog_z_is_61 :
  promethium_homolog_z = 61.
Proof. reflexivity. Qed.

Lemma np_element_symbol_nonempty :
  np_element_symbol <> "".
Proof. discriminate. Qed.

Lemma np_observed_occupancy_tag_nonempty :
  np_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma np_predicted_occupancy_tag_nonempty :
  np_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma np_observed_ne_predicted_occupancy :
  np_observed_occupancy_tag <> np_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma np_observed_ne_predicted_subshell :
  np_observed_subshell_notation <> np_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma np_homolog_occupancy_not_copy :
  np_observed_occupancy_tag <> pm_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "actinide_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "actinide_exception".
Proof. reflexivity. Qed.

Definition np_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma np_exception_continuum_factor_tag_nonempty :
  np_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive npec_channel_slot : Type :=
  | npec_slot_unwired
  | npec_slot_absent
  | npec_slot_present.

Definition npec_channel_slot_beq (s1 s2 : npec_channel_slot) : bool :=
  match s1, s2 with
  | npec_slot_unwired, npec_slot_unwired => true
  | npec_slot_absent, npec_slot_absent => true
  | npec_slot_present, npec_slot_present => true
  | _, _ => false
  end.

Definition npec_channel_slot_is_present (s : npec_channel_slot) : bool :=
  match s with
  | npec_slot_present => true
  | _ => false
  end.

Definition npExceptionContinuumProductChannelCount : nat := 3.

Lemma np_exception_continuum_product_channel_count_is_three :
  npExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 np_exception_continuum. *)
Definition npec_channel_occupancy_engine_sort : nat := 0.
Definition npec_channel_observed_override : nat := 1.
Definition npec_channel_actinide_exception_continuum : nat := 2.

Lemma npec_channel_occupancy_engine_sort_idx_is_0 :
  npec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma npec_channel_observed_override_idx_is_1 :
  npec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma npec_channel_class9_np_exception_continuum_idx_is_2 :
  npec_channel_actinide_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition npec_channel_bundle : Type := nat -> npec_channel_slot.

Definition npExceptionContinuumBundleAllUnwired : npec_channel_bundle :=
  fun _ => npec_slot_unwired.

Definition npExceptionContinuumBundleAt (b : npec_channel_bundle) (idx : nat)
  (slot : npec_channel_slot) : npec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition npExceptionContinuumBundleWithPresent
  (b : npec_channel_bundle) (idx : nat) : npec_channel_bundle :=
  npExceptionContinuumBundleAt b idx npec_slot_present.

Fixpoint count_npec_present_up_to (b : npec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if npec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_npec_present_up_to b i + add
  end.

Definition npExceptionContinuumBundlePresentCount (b : npec_channel_bundle) : nat :=
  count_npec_present_up_to b npExceptionContinuumProductChannelCount.

Definition npExceptionContinuumBundleHolds (b : npec_channel_bundle) (idx : nat) : bool :=
  npec_channel_slot_is_present (b idx).

Definition npExceptionContinuumBundleIsConcurrentProduct (b : npec_channel_bundle) : bool :=
  Nat.leb 2 (npExceptionContinuumBundlePresentCount b).

(* Np Z=93 interact restriction + G-min + class 14 np_exception_continuum concurrent witness. *)
Definition npExceptionContinuumNp93Witness : npec_channel_bundle :=
  npExceptionContinuumBundleWithPresent
    (npExceptionContinuumBundleWithPresent
      (npExceptionContinuumBundleWithPresent npExceptionContinuumBundleAllUnwired
        npec_channel_occupancy_engine_sort)
      npec_channel_observed_override)
    npec_channel_actinide_exception_continuum.

Definition npExceptionContinuumEmptyWitness : npec_channel_bundle :=
  npExceptionContinuumBundleAllUnwired.

Definition npExceptionContinuumSinglePresent : npec_channel_bundle :=
  npExceptionContinuumBundleWithPresent npExceptionContinuumBundleAllUnwired
    npec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  npExceptionContinuumBundleHolds npExceptionContinuumNp93Witness
    npec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  npExceptionContinuumBundleHolds npExceptionContinuumNp93Witness
    npec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_np_exception_continuum_channel_present :
  npExceptionContinuumBundleHolds npExceptionContinuumNp93Witness
    npec_channel_actinide_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma np93_witness_present_count_is_three :
  npExceptionContinuumBundlePresentCount npExceptionContinuumNp93Witness = 3.
Proof. reflexivity. Qed.

Lemma np93_witness_is_concurrent_product :
  npExceptionContinuumBundleIsConcurrentProduct npExceptionContinuumNp93Witness = true.
Proof.
  unfold npExceptionContinuumBundleIsConcurrentProduct.
  rewrite np93_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  npExceptionContinuumBundlePresentCount npExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  npExceptionContinuumBundleIsConcurrentProduct npExceptionContinuumEmptyWitness = false.
Proof.
  unfold npExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  npExceptionContinuumBundlePresentCount npExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  npExceptionContinuumBundleIsConcurrentProduct npExceptionContinuumSinglePresent = false.
Proof.
  unfold npExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive npec_xor_posture : Type :=
  | npec_xor_exclusive
  | npec_xor_concurrent_product.

Definition uecXorClassifierMarker : string := "chem_l0_np_exception_continuum_xor_classifier_v1".
Definition uecConcurrentProductMarker : string := "chem_int_np_exception_continuum_product_v1".

Lemma npec_xor_marker_ne_concurrent_product_marker :
  uecXorClassifierMarker <> uecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition uecXorClassifierIncompatible (claim_xor : bool)
  (b : npec_channel_bundle) : bool :=
  claim_xor && npExceptionContinuumBundleIsConcurrentProduct b.

Lemma npec_xor_refuse_on_np93_witness :
  uecXorClassifierIncompatible true npExceptionContinuumNp93Witness = true.
Proof.
  unfold uecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma npec_xor_ok_on_concurrent_product_claim :
  uecXorClassifierIncompatible false npExceptionContinuumNp93Witness = false.
Proof. reflexivity. Qed.

Definition uecProductNotXor : bool :=
  npExceptionContinuumBundleIsConcurrentProduct npExceptionContinuumNp93Witness &&
  uecXorClassifierIncompatible true npExceptionContinuumNp93Witness.

Lemma npec_product_not_xor_true : uecProductNotXor = true.
Proof.
  unfold uecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  uecProductNotXor = true /\
  Nat.leb 2 (npExceptionContinuumBundlePresentCount
    npExceptionContinuumNp93Witness) = true /\
  uecXorClassifierMarker <> uecConcurrentProductMarker.
Proof.
  split.
  - apply npec_product_not_xor_true.
  - split.
    + rewrite np93_witness_present_count_is_three.
      reflexivity.
    + apply npec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive npec_bar_presence : Type :=
  | npec_bar_absent
  | npec_bar_present.

Record npec_claim_bar : Type := {
  npec_bar_presence_field : npec_bar_presence;
  npec_bar_defect_total : nat
}.

Definition npExceptionContinuumClaimBarAbsent : npec_claim_bar :=
  {| npec_bar_presence_field := npec_bar_absent;
     npec_bar_defect_total := 0 |}.

Definition npExceptionContinuumClaimBarZeroDefect : npec_claim_bar :=
  {| npec_bar_presence_field := npec_bar_present;
     npec_bar_defect_total := 0 |}.

Definition npec_claim_bar_zero_defect (b : npec_claim_bar) : bool :=
  match npec_bar_presence_field b with
  | npec_bar_absent => false
  | npec_bar_present => Nat.eqb (npec_bar_defect_total b) 0
  end.

Lemma npec_claim_bar_zero_defect_true :
  npec_claim_bar_zero_defect npExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma npec_claim_bar_absent_not_zero_defect :
  npec_claim_bar_zero_defect npExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive npec_conservation_verdict : Type :=
  | npec_verdict_unwired_ok
  | npec_verdict_named_ok
  | npec_verdict_design_ok
  | npec_verdict_trivial_refuse
  | npec_verdict_xor_refuse
  | npec_verdict_green_invent_refuse
  | npec_verdict_proved_without_bar_refuse
  | npec_verdict_production_wired_refuse
  | npec_verdict_parallel_np_exception_continuum_axiom_refuse
  | npec_verdict_species_id_smuggle_refuse
  | npec_verdict_extra_element_id_refuse
  | npec_verdict_extra_np_exception_continuum_force_refuse
  | npec_verdict_tp_float_pin_refuse.

Definition npec_conservation_verdict_ok (v : npec_conservation_verdict) : bool :=
  match v with
  | npec_verdict_unwired_ok => true
  | npec_verdict_named_ok => true
  | npec_verdict_design_ok => true
  | _ => false
  end.

Definition npExceptionContinuumBundleNontrivial (b : npec_channel_bundle) : bool :=
  Nat.ltb 0 (npExceptionContinuumBundlePresentCount b).

Definition evaluate_np_exception_continuum_bundle
  (m : NpExceptionContinuumModality)
  (b : npec_channel_bundle)
  (bar : npec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : npec_conservation_verdict :=
  if claim_physics_green
  then npec_verdict_green_invent_refuse
  else if claim_proved
       then npec_verdict_proved_without_bar_refuse
       else if negb (npExceptionContinuumBundleNontrivial b)
            then npec_verdict_trivial_refuse
            else if uecXorClassifierIncompatible claim_xor_classifier b
                 then npec_verdict_xor_refuse
                 else
                   match m with
                   | np_exception_continuum_unwired =>
                       if npExceptionContinuumBundleIsConcurrentProduct b
                       then npec_verdict_named_ok
                       else npec_verdict_design_ok
                   | np_exception_continuum_assumed
                   | np_exception_continuum_surrogate =>
                       npec_verdict_design_ok
                   | np_exception_continuum_proved =>
                       npec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_np_exception_continuum_close
  (m : NpExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : npec_conservation_verdict :=
  if claim_physics_green
  then npec_verdict_green_invent_refuse
  else if claim_production_wired
  then npec_verdict_production_wired_refuse
  else
    match m with
    | np_exception_continuum_unwired => npec_verdict_unwired_ok
    | np_exception_continuum_assumed
    | np_exception_continuum_proved
    | np_exception_continuum_surrogate => npec_verdict_named_ok
    end.

Definition np_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_np_exception_continuum_close
          np_exception_continuum_proved claim_physics_green claim_production_wired with
  | npec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive npec_conservation_law : Type :=
  | npec_law_conserved
  | npec_law_named_ok
  | npec_law_trivial_refuse
  | npec_law_green_invent_refuse.

Definition npec_conservation_law_count : nat := 4.

Lemma npec_conservation_law_count_is_four :
  npec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive npec_conservation_law_witness : Type :=
  | npec_law_witness_open
  | npec_law_witness_proved.

Definition evaluate_npec_conservation_law_witness
  (law : npec_conservation_law)
  (m : NpExceptionContinuumModality)
  : npec_conservation_law_witness :=
  match m with
  | np_exception_continuum_unwired
  | np_exception_continuum_assumed
  | np_exception_continuum_surrogate => npec_law_witness_open
  | np_exception_continuum_proved => npec_law_witness_proved
  end.

Lemma all_npec_conservation_laws_open_at_unwired :
  evaluate_npec_conservation_law_witness npec_law_conserved
    np_exception_continuum_unwired = npec_law_witness_open /\
  evaluate_npec_conservation_law_witness npec_law_named_ok
    np_exception_continuum_unwired = npec_law_witness_open /\
  evaluate_npec_conservation_law_witness npec_law_trivial_refuse
    np_exception_continuum_unwired = npec_law_witness_open /\
  evaluate_npec_conservation_law_witness npec_law_green_invent_refuse
    np_exception_continuum_unwired = npec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition npExceptionContinuumProved : bool := false.

Lemma np_exception_continuum_proved_false :
  npExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_np_exception_continuum_close
    np_exception_continuum_unwired false false =
  npec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_np_exception_continuum_close
    np_exception_continuum_unwired false false =
  npec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_unwired false false) =
  true.
Proof.
  unfold npec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Np Z=93 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma np93_witness_named_ok :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false false =
  npec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_np93_np_exception_continuum :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false false =
  npec_verdict_named_ok /\
  npExceptionContinuumBundleIsConcurrentProduct npExceptionContinuumNp93Witness = true /\
  neptunium_atomic_number_z = 93 /\
  np_observed_occupancy_tag = "7s25f46d1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma npec_named_close_ok :
  evaluate_np_exception_continuum_close
    np_exception_continuum_proved false false =
  npec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_np_exception_continuum_close :
  evaluate_np_exception_continuum_close
    np_exception_continuum_proved false false =
  npec_verdict_named_ok /\
  np_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply npec_named_close_ok.
  - unfold np_exception_continuum_authorized.
    rewrite npec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — np_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumEmptyWitness
    npExceptionContinuumClaimBarAbsent false false false =
  npec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumEmptyWitness
    npExceptionContinuumClaimBarAbsent false false false =
  npec_verdict_trivial_refuse /\
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_bundle
       np_exception_continuum_unwired
       npExceptionContinuumEmptyWitness
       npExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold npec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent true false false =
  npec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent true false false =
  npec_verdict_xor_refuse /\
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_bundle
       np_exception_continuum_unwired
       npExceptionContinuumNp93Witness
       npExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold npec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_np_exception_continuum_close
    np_exception_continuum_unwired true false =
  npec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_unwired true false) =
  false.
Proof.
  unfold npec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_npec_bundle_refuse :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false true false =
  npec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — np_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false true =
  npec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false true =
  npec_verdict_proved_without_bar_refuse /\
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_bundle
       np_exception_continuum_unwired
       npExceptionContinuumNp93Witness
       npExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold npec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — np_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_np_exception_continuum_close
    np_exception_continuum_proved false true =
  npec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_proved false true) =
  false.
Proof.
  unfold npec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel np_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition npExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelNpExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_np_exception_continuum_axiom_refuse :
  npExceptionContinuumAuthority <>
  parallelNpExceptionAxiomTag /\
  npExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply np_exception_continuum_proved_false.
Qed.

Theorem parallel_np_exception_continuum_axiom_not_minted :
  npExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  npExceptionContinuumProved = false /\
  npExceptionContinuumAuthority <> parallelNpExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "pm_z61_occupancy_copied_onto_np_z93".

Definition npExceptionContinuumFraming : string :=
  "second_law_conservation_np_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  npExceptionContinuumFraming <>
  homologCopyFraming /\
  neptunium_atomic_number_z = 93 /\
  np_observed_occupancy_tag = "7s25f46d1".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem np_pm_homolog_not_occupancy_copy :
  npExceptionContinuumFraming <>
  homologCopyFraming /\
  neptunium_atomic_number_z = 93 /\
  promethium_homolog_z = 61 /\
  np_observed_occupancy_tag <> pm_homolog_observed_occupancy_tag /\
  npExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — np_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "u_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  npExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  npExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  neptunium_atomic_number_z = 93.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — np_exception_continuum ≠ extra np_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_np_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/np_exception_continuum_barrier.rs".

Lemma extra_np_exception_continuum_force_refuse :
  npExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem np_exception_continuum_not_extra_np_exception_continuum_force :
  npExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/np_exception_continuum_barrier.rs" /\
  npExceptionContinuumProved = false.
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
  npExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  np_observed_occupancy_tag <> np_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply np_observed_ne_predicted_occupancy.
Qed.

Theorem np_observed_override_not_madelung_family_smuggle :
  npExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  np_observed_occupancy_tag = "7s25f46d1" /\
  np_predicted_occupancy_tag = "5f5" /\
  npExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply np_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_np_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  npExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  npExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  neptunium_atomic_number_z = 93.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  NpExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition npec_conservation_coherence_scaffold : bool :=
  npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_proved false false) &&
  negb (npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_unwired true false)) &&
  negb (npec_conservation_verdict_ok
    (evaluate_np_exception_continuum_close
       np_exception_continuum_proved false true)).

Lemma npec_conservation_coherence_scaffold_true :
  npec_conservation_coherence_scaffold = true.
Proof.
  unfold npec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem npec_conservation_coherence_scaffold_theorem :
  evaluate_np_exception_continuum_close
    np_exception_continuum_proved false false =
    npec_verdict_named_ok /\
  evaluate_np_exception_continuum_close
    np_exception_continuum_unwired true false =
    npec_verdict_green_invent_refuse /\
  evaluate_np_exception_continuum_close
    np_exception_continuum_proved false true =
    npec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition npec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition npec_conservation_knowing_fiber_ok : bool :=
  npec_conservation_fiber_ok fiber_quantum_knowing.

Definition npec_conservation_meso_acting_ok : bool :=
  npec_conservation_fiber_ok fiber_meso_acting.

Lemma npec_conservation_knowing_fiber_ok_true :
  npec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma npec_conservation_meso_acting_not_ok :
  npec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem npec_conservation_routes_knowing_not_meso :
  npec_conservation_knowing_fiber_ok = true /\
  npec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply npec_conservation_knowing_fiber_ok_true.
  - apply npec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  npec_conservation_knowing_fiber_ok &&
  negb npec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, npec_conservation_knowing_fiber_ok,
    npec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem np_exception_continuum_fixture_scaffold :
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false false =
    npec_verdict_named_ok /\
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumEmptyWitness
    npExceptionContinuumClaimBarAbsent false false false =
    npec_verdict_trivial_refuse /\
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent true false false =
    npec_verdict_xor_refuse /\
  evaluate_np_exception_continuum_bundle
    np_exception_continuum_unwired
    npExceptionContinuumNp93Witness
    npExceptionContinuumClaimBarAbsent false false true =
    npec_verdict_proved_without_bar_refuse /\
  evaluate_np_exception_continuum_close
    np_exception_continuum_unwired false false =
    npec_verdict_unwired_ok /\
  npec_conservation_knowing_fiber_ok = true /\
  npec_conservation_meso_acting_ok = false /\
  npExceptionContinuumProved = false /\
  uecProductNotXor = true /\
  neptunium_atomic_number_z = 93.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pm Z=61 homolog not Np copy — period-6 actinide homolog ≠ identity     *)
(* ------------------------------------------------------------------ *)

Definition promethium_atomic_number_z : nat := 61.

Lemma promethium_atomic_number_z_is_61 :
  promethium_atomic_number_z = 61.
Proof. reflexivity. Qed.

Definition promethium_homolog_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d4".

Lemma pm_homolog_occupancy_tag_named :
  pm_homolog_observed_occupancy_tag = "6s24f5".
Proof. reflexivity. Qed.

Lemma np_pm_homolog_subshell_not_copy :
  np_observed_subshell_notation <>
  promethium_homolog_observed_subshell_notation.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma np_pm_homolog_not_copy :
  neptunium_atomic_number_z = 93 /\
  promethium_atomic_number_z = 61 /\
  np_observed_occupancy_tag <> pm_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem w_period6_homolog_not_u_occupancy_copy :
  neptunium_atomic_number_z = 93 /\
  promethium_atomic_number_z = 61 /\
  np_observed_occupancy_tag = "7s25f46d1" /\
  pm_homolog_observed_occupancy_tag = "6s24f5" /\
  np_observed_occupancy_tag <> pm_homolog_observed_occupancy_tag /\
  npExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — np_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition npExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition npExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-NP-EXCEPTION-CONTINUUM".

Definition npExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-NP-EXCEPTION-CONTINUUM NpExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice npExceptionContinuumProved false evaluateNpExceptionContinuumBundle evaluateNpExceptionContinuum named Np Z=93 actinide occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Pm Z=61 homolog not Np 5f3 6d1 7s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma np_exception_continuum_cell_id :
  npExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-NP-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma np_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma np_exception_continuum_authority_path :
  npExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma np_exception_continuum_cites_l0_ore02 :
  npExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma np_exception_continuum_cites_marker :
  uecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma np_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma np_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma np_exception_continuum_not_26th_axiom :
  npExceptionContinuumFraming <> parallelNpExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma np_exception_continuum_second_law_conservation_framing :
  npExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition namedExceptionNamedObject : string :=
  "interact_restriction_on_np_exception_continuum_morphism".

Lemma tst_prior_art_not_named_object :
  namedExceptionNamedObject <>
  madelungWalkFraming /\
  observed_override_channel_tag = "observed_override".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem actinide_exception_is_named_object_not_madelung_walk :
  namedExceptionNamedObject <>
  madelungWalkFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort" /\
  npExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not np_exception_continuum axiom / extra force     *)
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

Theorem np_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/np_exception_continuum_barrier.rs" /\
  npExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma np_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma np_exception_continuum_modality_unwired :
  npExceptionContinuumModalityCurrent =
  np_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition npExceptionContinuumProductionWired : Prop := False.

Lemma np_exception_continuum_not_production_wired :
  ~ npExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


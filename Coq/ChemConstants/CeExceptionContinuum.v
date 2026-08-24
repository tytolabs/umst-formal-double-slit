(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CeExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Ce Z=58 NamedException occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Ce Z=58 4f1 5d1 6s2 NamedException; Th Z=90 period-7 homolog not Ce occupancy copy. *)
(*  ceExceptionContinuumProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs (read-only). *)
(*  INT: umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs (cite). *)
(*  INT: umst/umst-chem/src/qlattice.rs (read-only cite).               *)
(*  NamedOccupancyExceptions.v cited. OccupancyEngineSort.v cited.      *)
(* ================================================================== *)


From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **ce_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive CeExceptionContinuumModality : Type :=
  | ce_exception_continuum_unwired
  | ce_exception_continuum_assumed
  | ce_exception_continuum_proved
  | ce_exception_continuum_surrogate.

Definition ceExceptionContinuumModalityCurrent :
  CeExceptionContinuumModality :=
  ce_exception_continuum_unwired.

Definition ce_exception_continuum_lattice_cardinality : nat := 4.

Lemma ce_exception_continuum_lattice_cardinality_is_four :
  ce_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma ce_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb ce_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold ce_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — ce_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_ce_exception_continuum_idx : nat := 14.

Lemma pattern_class_ce_exception_continuum_idx_is_14 :
  pattern_class_ce_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma ce_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_ce_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_ce_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_ce_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_ce_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_ce_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_ce_exception_continuum_tag_nonempty :
  pattern_class_ce_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_ce_exception_continuum_tag_nonempty :
  north_star_class_14_ce_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Ce Z=58 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition cerium_atomic_number_z : nat := 58.

Lemma cerium_atomic_number_z_is_58 :
  cerium_atomic_number_z = 58.
Proof. reflexivity. Qed.

Definition cerium_z_valid : bool :=
  Nat.ltb 0 cerium_atomic_number_z &&
  Nat.leb cerium_atomic_number_z iupac_table_cardinality.

Lemma cerium_z_valid_true : cerium_z_valid = true.
Proof.
  unfold cerium_z_valid, cerium_atomic_number_z, iupac_table_cardinality.
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
(*  Ce Z=58 occupancy pins — 4f¹5d¹6s² observed vs Madelung predicted  *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition ce_element_symbol : string := "Ce".

Definition ce_observed_occupancy_tag : string := "4f15d16s2".

Definition ce_predicted_occupancy_tag : string := "4f26s2".

Definition ce_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1".

Definition ce_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f2".

Definition th_homolog_observed_occupancy_tag : string := "6d27s2".

Definition thorium_homolog_z : nat := 90.

Lemma thorium_homolog_z_is_90 :
  thorium_homolog_z = 90.
Proof. reflexivity. Qed.

Lemma ce_element_symbol_nonempty :
  ce_element_symbol <> "".
Proof. discriminate. Qed.

Lemma ce_observed_occupancy_tag_nonempty :
  ce_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma ce_predicted_occupancy_tag_nonempty :
  ce_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma ce_observed_ne_predicted_occupancy :
  ce_observed_occupancy_tag <> ce_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma ce_observed_ne_predicted_subshell :
  ce_observed_subshell_notation <> ce_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma ce_homolog_occupancy_not_copy :
  ce_observed_occupancy_tag <> th_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "named_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "named_exception".
Proof. reflexivity. Qed.

Definition ce_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma ce_exception_continuum_factor_tag_nonempty :
  ce_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive ceec_channel_slot : Type :=
  | ceec_slot_unwired
  | ceec_slot_absent
  | ceec_slot_present.

Definition ceec_channel_slot_beq (s1 s2 : ceec_channel_slot) : bool :=
  match s1, s2 with
  | ceec_slot_unwired, ceec_slot_unwired => true
  | ceec_slot_absent, ceec_slot_absent => true
  | ceec_slot_present, ceec_slot_present => true
  | _, _ => false
  end.

Definition ceec_channel_slot_is_present (s : ceec_channel_slot) : bool :=
  match s with
  | ceec_slot_present => true
  | _ => false
  end.

Definition ceExceptionContinuumProductChannelCount : nat := 3.

Lemma ce_exception_continuum_product_channel_count_is_three :
  ceExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 ce_exception_continuum. *)
Definition ceec_channel_occupancy_engine_sort : nat := 0.
Definition ceec_channel_observed_override : nat := 1.
Definition ceec_channel_named_exception_continuum : nat := 2.

Lemma ceec_channel_occupancy_engine_sort_idx_is_0 :
  ceec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma ceec_channel_observed_override_idx_is_1 :
  ceec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma ceec_channel_class9_ce_exception_continuum_idx_is_2 :
  ceec_channel_named_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition ceec_channel_bundle : Type := nat -> ceec_channel_slot.

Definition ceExceptionContinuumBundleAllUnwired : ceec_channel_bundle :=
  fun _ => ceec_slot_unwired.

Definition ceExceptionContinuumBundleAt (b : ceec_channel_bundle) (idx : nat)
  (slot : ceec_channel_slot) : ceec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition ceExceptionContinuumBundleWithPresent
  (b : ceec_channel_bundle) (idx : nat) : ceec_channel_bundle :=
  ceExceptionContinuumBundleAt b idx ceec_slot_present.

Fixpoint count_ceec_present_up_to (b : ceec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if ceec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_ceec_present_up_to b i + add
  end.

Definition ceExceptionContinuumBundlePresentCount (b : ceec_channel_bundle) : nat :=
  count_ceec_present_up_to b ceExceptionContinuumProductChannelCount.

Definition ceExceptionContinuumBundleHolds (b : ceec_channel_bundle) (idx : nat) : bool :=
  ceec_channel_slot_is_present (b idx).

Definition ceExceptionContinuumBundleIsConcurrentProduct (b : ceec_channel_bundle) : bool :=
  Nat.leb 2 (ceExceptionContinuumBundlePresentCount b).

(* Ce Z=58 interact restriction + G-min + class 14 ce_exception_continuum concurrent witness. *)
Definition ceExceptionContinuumCe58Witness : ceec_channel_bundle :=
  ceExceptionContinuumBundleWithPresent
    (ceExceptionContinuumBundleWithPresent
      (ceExceptionContinuumBundleWithPresent ceExceptionContinuumBundleAllUnwired
        ceec_channel_occupancy_engine_sort)
      ceec_channel_observed_override)
    ceec_channel_named_exception_continuum.

Definition ceExceptionContinuumEmptyWitness : ceec_channel_bundle :=
  ceExceptionContinuumBundleAllUnwired.

Definition ceExceptionContinuumSinglePresent : ceec_channel_bundle :=
  ceExceptionContinuumBundleWithPresent ceExceptionContinuumBundleAllUnwired
    ceec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  ceExceptionContinuumBundleHolds ceExceptionContinuumCe58Witness
    ceec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  ceExceptionContinuumBundleHolds ceExceptionContinuumCe58Witness
    ceec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_ce_exception_continuum_channel_present :
  ceExceptionContinuumBundleHolds ceExceptionContinuumCe58Witness
    ceec_channel_named_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma ce58_witness_present_count_is_three :
  ceExceptionContinuumBundlePresentCount ceExceptionContinuumCe58Witness = 3.
Proof. reflexivity. Qed.

Lemma ce58_witness_is_concurrent_product :
  ceExceptionContinuumBundleIsConcurrentProduct ceExceptionContinuumCe58Witness = true.
Proof.
  unfold ceExceptionContinuumBundleIsConcurrentProduct.
  rewrite ce58_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  ceExceptionContinuumBundlePresentCount ceExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  ceExceptionContinuumBundleIsConcurrentProduct ceExceptionContinuumEmptyWitness = false.
Proof.
  unfold ceExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  ceExceptionContinuumBundlePresentCount ceExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  ceExceptionContinuumBundleIsConcurrentProduct ceExceptionContinuumSinglePresent = false.
Proof.
  unfold ceExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ceec_xor_posture : Type :=
  | ceec_xor_exclusive
  | ceec_xor_concurrent_product.

Definition ceecXorClassifierMarker : string := "chem_l0_ce_exception_continuum_xor_classifier_v1".
Definition ceecConcurrentProductMarker : string := "chem_int_ce_exception_continuum_product_v1".

Lemma ceec_xor_marker_ne_concurrent_product_marker :
  ceecXorClassifierMarker <> ceecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition ceecXorClassifierIncompatible (claim_xor : bool)
  (b : ceec_channel_bundle) : bool :=
  claim_xor && ceExceptionContinuumBundleIsConcurrentProduct b.

Lemma ceec_xor_refuse_on_ce58_witness :
  ceecXorClassifierIncompatible true ceExceptionContinuumCe58Witness = true.
Proof.
  unfold ceecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma ceec_xor_ok_on_concurrent_product_claim :
  ceecXorClassifierIncompatible false ceExceptionContinuumCe58Witness = false.
Proof. reflexivity. Qed.

Definition ceecProductNotXor : bool :=
  ceExceptionContinuumBundleIsConcurrentProduct ceExceptionContinuumCe58Witness &&
  ceecXorClassifierIncompatible true ceExceptionContinuumCe58Witness.

Lemma ceec_product_not_xor_true : ceecProductNotXor = true.
Proof.
  unfold ceecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  ceecProductNotXor = true /\
  Nat.leb 2 (ceExceptionContinuumBundlePresentCount
    ceExceptionContinuumCe58Witness) = true /\
  ceecXorClassifierMarker <> ceecConcurrentProductMarker.
Proof.
  split.
  - apply ceec_product_not_xor_true.
  - split.
    + rewrite ce58_witness_present_count_is_three.
      reflexivity.
    + apply ceec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive ceec_bar_presence : Type :=
  | ceec_bar_absent
  | ceec_bar_present.

Record ceec_claim_bar : Type := {
  ceec_bar_presence_field : ceec_bar_presence;
  ceec_bar_defect_total : nat
}.

Definition ceExceptionContinuumClaimBarAbsent : ceec_claim_bar :=
  {| ceec_bar_presence_field := ceec_bar_absent;
     ceec_bar_defect_total := 0 |}.

Definition ceExceptionContinuumClaimBarZeroDefect : ceec_claim_bar :=
  {| ceec_bar_presence_field := ceec_bar_present;
     ceec_bar_defect_total := 0 |}.

Definition ceec_claim_bar_zero_defect (b : ceec_claim_bar) : bool :=
  match ceec_bar_presence_field b with
  | ceec_bar_absent => false
  | ceec_bar_present => Nat.eqb (ceec_bar_defect_total b) 0
  end.

Lemma ceec_claim_bar_zero_defect_true :
  ceec_claim_bar_zero_defect ceExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma ceec_claim_bar_absent_not_zero_defect :
  ceec_claim_bar_zero_defect ceExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive ceec_conservation_verdict : Type :=
  | ceec_verdict_unwired_ok
  | ceec_verdict_named_ok
  | ceec_verdict_design_ok
  | ceec_verdict_trivial_refuse
  | ceec_verdict_xor_refuse
  | ceec_verdict_green_invent_refuse
  | ceec_verdict_proved_without_bar_refuse
  | ceec_verdict_production_wired_refuse
  | ceec_verdict_parallel_ce_exception_continuum_axiom_refuse
  | ceec_verdict_species_id_smuggle_refuse
  | ceec_verdict_extra_element_id_refuse
  | ceec_verdict_extra_ce_exception_continuum_force_refuse
  | ceec_verdict_tp_float_pin_refuse.

Definition ceec_conservation_verdict_ok (v : ceec_conservation_verdict) : bool :=
  match v with
  | ceec_verdict_unwired_ok => true
  | ceec_verdict_named_ok => true
  | ceec_verdict_design_ok => true
  | _ => false
  end.

Definition ceExceptionContinuumBundleNontrivial (b : ceec_channel_bundle) : bool :=
  Nat.ltb 0 (ceExceptionContinuumBundlePresentCount b).

Definition evaluate_ce_exception_continuum_bundle
  (m : CeExceptionContinuumModality)
  (b : ceec_channel_bundle)
  (bar : ceec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : ceec_conservation_verdict :=
  if claim_physics_green
  then ceec_verdict_green_invent_refuse
  else if claim_proved
       then ceec_verdict_proved_without_bar_refuse
       else if negb (ceExceptionContinuumBundleNontrivial b)
            then ceec_verdict_trivial_refuse
            else if ceecXorClassifierIncompatible claim_xor_classifier b
                 then ceec_verdict_xor_refuse
                 else
                   match m with
                   | ce_exception_continuum_unwired =>
                       if ceExceptionContinuumBundleIsConcurrentProduct b
                       then ceec_verdict_named_ok
                       else ceec_verdict_design_ok
                   | ce_exception_continuum_assumed
                   | ce_exception_continuum_surrogate =>
                       ceec_verdict_design_ok
                   | ce_exception_continuum_proved =>
                       ceec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_ce_exception_continuum_close
  (m : CeExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : ceec_conservation_verdict :=
  if claim_physics_green
  then ceec_verdict_green_invent_refuse
  else if claim_production_wired
  then ceec_verdict_production_wired_refuse
  else
    match m with
    | ce_exception_continuum_unwired => ceec_verdict_unwired_ok
    | ce_exception_continuum_assumed
    | ce_exception_continuum_proved
    | ce_exception_continuum_surrogate => ceec_verdict_named_ok
    end.

Definition ce_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_ce_exception_continuum_close
          ce_exception_continuum_proved claim_physics_green claim_production_wired with
  | ceec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive ceec_conservation_law : Type :=
  | ceec_law_conserved
  | ceec_law_named_ok
  | ceec_law_trivial_refuse
  | ceec_law_green_invent_refuse.

Definition ceec_conservation_law_count : nat := 4.

Lemma ceec_conservation_law_count_is_four :
  ceec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive ceec_conservation_law_witness : Type :=
  | ceec_law_witness_open
  | ceec_law_witness_proved.

Definition evaluate_ceec_conservation_law_witness
  (law : ceec_conservation_law)
  (m : CeExceptionContinuumModality)
  : ceec_conservation_law_witness :=
  match m with
  | ce_exception_continuum_unwired
  | ce_exception_continuum_assumed
  | ce_exception_continuum_surrogate => ceec_law_witness_open
  | ce_exception_continuum_proved => ceec_law_witness_proved
  end.

Lemma all_ceec_conservation_laws_open_at_unwired :
  evaluate_ceec_conservation_law_witness ceec_law_conserved
    ce_exception_continuum_unwired = ceec_law_witness_open /\
  evaluate_ceec_conservation_law_witness ceec_law_named_ok
    ce_exception_continuum_unwired = ceec_law_witness_open /\
  evaluate_ceec_conservation_law_witness ceec_law_trivial_refuse
    ce_exception_continuum_unwired = ceec_law_witness_open /\
  evaluate_ceec_conservation_law_witness ceec_law_green_invent_refuse
    ce_exception_continuum_unwired = ceec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition ceExceptionContinuumProved : bool := false.

Lemma ce_exception_continuum_proved_false :
  ceExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_unwired false false =
  ceec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_unwired false false =
  ceec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_unwired false false) =
  true.
Proof.
  unfold ceec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Ce Z=58 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma ce58_witness_named_ok :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false false =
  ceec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ce58_ce_exception_continuum :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false false =
  ceec_verdict_named_ok /\
  ceExceptionContinuumBundleIsConcurrentProduct ceExceptionContinuumCe58Witness = true /\
  cerium_atomic_number_z = 58 /\
  ce_observed_occupancy_tag = "4f15d16s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma ceec_named_close_ok :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_proved false false =
  ceec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ce_exception_continuum_close :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_proved false false =
  ceec_verdict_named_ok /\
  ce_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply ceec_named_close_ok.
  - unfold ce_exception_continuum_authorized.
    rewrite ceec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — ce_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumEmptyWitness
    ceExceptionContinuumClaimBarAbsent false false false =
  ceec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumEmptyWitness
    ceExceptionContinuumClaimBarAbsent false false false =
  ceec_verdict_trivial_refuse /\
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_bundle
       ce_exception_continuum_unwired
       ceExceptionContinuumEmptyWitness
       ceExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold ceec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent true false false =
  ceec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent true false false =
  ceec_verdict_xor_refuse /\
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_bundle
       ce_exception_continuum_unwired
       ceExceptionContinuumCe58Witness
       ceExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold ceec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_unwired true false =
  ceec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_unwired true false) =
  false.
Proof.
  unfold ceec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ceec_bundle_refuse :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false true false =
  ceec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — ce_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false true =
  ceec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false true =
  ceec_verdict_proved_without_bar_refuse /\
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_bundle
       ce_exception_continuum_unwired
       ceExceptionContinuumCe58Witness
       ceExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold ceec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — ce_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_proved false true =
  ceec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_proved false true) =
  false.
Proof.
  unfold ceec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel ce_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition ceExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelCeExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_ce_exception_continuum_axiom_refuse :
  ceExceptionContinuumAuthority <>
  parallelCeExceptionAxiomTag /\
  ceExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply ce_exception_continuum_proved_false.
Qed.

Theorem parallel_ce_exception_continuum_axiom_not_minted :
  ceExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  ceExceptionContinuumProved = false /\
  ceExceptionContinuumAuthority <> parallelCeExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "th_z90_occupancy_copied_onto_ce_z58".

Definition ceExceptionContinuumFraming : string :=
  "second_law_conservation_ce_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  ceExceptionContinuumFraming <>
  homologCopyFraming /\
  cerium_atomic_number_z = 58 /\
  ce_observed_occupancy_tag = "4f15d16s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ce_th_homolog_not_occupancy_copy :
  ceExceptionContinuumFraming <>
  homologCopyFraming /\
  cerium_atomic_number_z = 58 /\
  thorium_homolog_z = 90 /\
  ce_observed_occupancy_tag <> th_homolog_observed_occupancy_tag /\
  ceExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — ce_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "ce_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  ceExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  ceExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  cerium_atomic_number_z = 58.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — ce_exception_continuum ≠ extra ce_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_ce_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/ce_exception_continuum_barrier.rs".

Lemma extra_ce_exception_continuum_force_refuse :
  ceExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem ce_exception_continuum_not_extra_ce_exception_continuum_force :
  ceExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/ce_exception_continuum_barrier.rs" /\
  ceExceptionContinuumProved = false.
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
  ceExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  ce_observed_occupancy_tag <> ce_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply ce_observed_ne_predicted_occupancy.
Qed.

Theorem ce_observed_override_not_madelung_family_smuggle :
  ceExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  ce_observed_occupancy_tag = "4f15d16s2" /\
  ce_predicted_occupancy_tag = "4f26s2" /\
  ceExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply ce_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_ce_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  ceExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  ceExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  cerium_atomic_number_z = 58.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  CeExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition ceec_conservation_coherence_scaffold : bool :=
  ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_proved false false) &&
  negb (ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_unwired true false)) &&
  negb (ceec_conservation_verdict_ok
    (evaluate_ce_exception_continuum_close
       ce_exception_continuum_proved false true)).

Lemma ceec_conservation_coherence_scaffold_true :
  ceec_conservation_coherence_scaffold = true.
Proof.
  unfold ceec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem ceec_conservation_coherence_scaffold_theorem :
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_proved false false =
    ceec_verdict_named_ok /\
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_unwired true false =
    ceec_verdict_green_invent_refuse /\
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_proved false true =
    ceec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition ceec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition ceec_conservation_knowing_fiber_ok : bool :=
  ceec_conservation_fiber_ok fiber_quantum_knowing.

Definition ceec_conservation_meso_acting_ok : bool :=
  ceec_conservation_fiber_ok fiber_meso_acting.

Lemma ceec_conservation_knowing_fiber_ok_true :
  ceec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma ceec_conservation_meso_acting_not_ok :
  ceec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem ceec_conservation_routes_knowing_not_meso :
  ceec_conservation_knowing_fiber_ok = true /\
  ceec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply ceec_conservation_knowing_fiber_ok_true.
  - apply ceec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  ceec_conservation_knowing_fiber_ok &&
  negb ceec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, ceec_conservation_knowing_fiber_ok,
    ceec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem ce_exception_continuum_fixture_scaffold :
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false false =
    ceec_verdict_named_ok /\
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumEmptyWitness
    ceExceptionContinuumClaimBarAbsent false false false =
    ceec_verdict_trivial_refuse /\
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent true false false =
    ceec_verdict_xor_refuse /\
  evaluate_ce_exception_continuum_bundle
    ce_exception_continuum_unwired
    ceExceptionContinuumCe58Witness
    ceExceptionContinuumClaimBarAbsent false false true =
    ceec_verdict_proved_without_bar_refuse /\
  evaluate_ce_exception_continuum_close
    ce_exception_continuum_unwired false false =
    ceec_verdict_unwired_ok /\
  ceec_conservation_knowing_fiber_ok = true /\
  ceec_conservation_meso_acting_ok = false /\
  ceExceptionContinuumProved = false /\
  ceecProductNotXor = true /\
  cerium_atomic_number_z = 58.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Th Z=90 homolog not Ce copy — period-7 actinide homolog ≠ identity  *)
(* ------------------------------------------------------------------ *)

Definition thorium_atomic_number_z : nat := 90.

Lemma thorium_atomic_number_z_is_90 :
  thorium_atomic_number_z = 90.
Proof. reflexivity. Qed.

Definition thorium_homolog_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2".

Lemma th_homolog_occupancy_tag_named :
  th_homolog_observed_occupancy_tag = "6d27s2".
Proof. reflexivity. Qed.

Lemma ce_th_homolog_subshell_not_copy :
  ce_observed_subshell_notation <>
  thorium_homolog_observed_subshell_notation.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma ce_th_homolog_not_copy :
  cerium_atomic_number_z = 58 /\
  thorium_atomic_number_z = 90 /\
  ce_observed_occupancy_tag <> th_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem th_period7_homolog_not_ce_occupancy_copy :
  cerium_atomic_number_z = 58 /\
  thorium_atomic_number_z = 90 /\
  ce_observed_occupancy_tag = "4f15d16s2" /\
  th_homolog_observed_occupancy_tag = "6d27s2" /\
  ce_observed_occupancy_tag <> th_homolog_observed_occupancy_tag /\
  ceExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — ce_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition ceExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/NamedOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition ceExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-CE-EXCEPTION-CONTINUUM".

Definition ceExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CE-EXCEPTION-CONTINUUM CeExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice ceExceptionContinuumProved false evaluateCeExceptionContinuumBundle evaluateCeExceptionContinuum named Ce Z=58 d-block occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ag Z=47 homolog not Cu 3d10 4s1 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma ce_exception_continuum_cell_id :
  ceExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-CE-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma ce_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma ce_exception_continuum_authority_path :
  ceExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma ce_exception_continuum_cites_l0_ore02 :
  ceExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma ce_exception_continuum_cites_marker :
  ceecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma ce_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma ce_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma ce_exception_continuum_not_26th_axiom :
  ceExceptionContinuumFraming <> parallelCeExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma ce_exception_continuum_second_law_conservation_framing :
  ceExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition namedExceptionNamedObject : string :=
  "interact_restriction_on_ce_exception_continuum_morphism".

Lemma tst_prior_art_not_named_object :
  namedExceptionNamedObject <>
  madelungWalkFraming /\
  observed_override_channel_tag = "observed_override".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem named_exception_is_named_object_not_madelung_walk :
  namedExceptionNamedObject <>
  madelungWalkFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort" /\
  ceExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not ce_exception_continuum axiom / extra force     *)
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

Theorem ce_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/ce_exception_continuum_barrier.rs" /\
  ceExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma ce_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma ce_exception_continuum_modality_unwired :
  ceExceptionContinuumModalityCurrent =
  ce_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition ceExceptionContinuumProductionWired : Prop := False.

Lemma ce_exception_continuum_not_production_wired :
  ~ ceExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


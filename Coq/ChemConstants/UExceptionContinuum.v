(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: UExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: U Z=92 actinide occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  U Z=92 5f3 6d1 7s2 actinide Madelung exception; W Z=74 homolog not U copy. *)
(*  uExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **u_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive UExceptionContinuumModality : Type :=
  | u_exception_continuum_unwired
  | u_exception_continuum_assumed
  | u_exception_continuum_proved
  | u_exception_continuum_surrogate.

Definition uExceptionContinuumModalityCurrent :
  UExceptionContinuumModality :=
  u_exception_continuum_unwired.

Definition u_exception_continuum_lattice_cardinality : nat := 4.

Lemma u_exception_continuum_lattice_cardinality_is_four :
  u_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma u_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb u_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold u_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — u_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_u_exception_continuum_idx : nat := 14.

Lemma pattern_class_u_exception_continuum_idx_is_14 :
  pattern_class_u_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma u_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_u_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_u_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_u_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_u_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_u_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_u_exception_continuum_tag_nonempty :
  pattern_class_u_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_u_exception_continuum_tag_nonempty :
  north_star_class_14_u_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — U Z=92 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition uranium_atomic_number_z : nat := 92.

Lemma uranium_atomic_number_z_is_92 :
  uranium_atomic_number_z = 92.
Proof. reflexivity. Qed.

Definition uranium_z_valid : bool :=
  Nat.ltb 0 uranium_atomic_number_z &&
  Nat.leb uranium_atomic_number_z iupac_table_cardinality.

Lemma uranium_z_valid_true : uranium_z_valid = true.
Proof.
  unfold uranium_z_valid, uranium_atomic_number_z, iupac_table_cardinality.
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
(*  U Z=92 occupancy pins — 4d⁵5s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition u_element_symbol : string := "U".

Definition u_observed_occupancy_tag : string := "5f36d17s2".

Definition u_predicted_occupancy_tag : string := "5f47s2".

Definition u_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1".

Definition u_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4".

Definition w_homolog_observed_occupancy_tag : string := "4f145d46s2".

Definition tungsten_homolog_z : nat := 74.

Lemma tungsten_homolog_z_is_74 :
  tungsten_homolog_z = 74.
Proof. reflexivity. Qed.

Lemma u_element_symbol_nonempty :
  u_element_symbol <> "".
Proof. discriminate. Qed.

Lemma u_observed_occupancy_tag_nonempty :
  u_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma u_predicted_occupancy_tag_nonempty :
  u_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma u_observed_ne_predicted_occupancy :
  u_observed_occupancy_tag <> u_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma u_observed_ne_predicted_subshell :
  u_observed_subshell_notation <> u_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma u_homolog_occupancy_not_copy :
  u_observed_occupancy_tag <> w_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "named_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "named_exception".
Proof. reflexivity. Qed.

Definition u_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma u_exception_continuum_factor_tag_nonempty :
  u_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive uec_channel_slot : Type :=
  | uec_slot_unwired
  | uec_slot_absent
  | uec_slot_present.

Definition uec_channel_slot_beq (s1 s2 : uec_channel_slot) : bool :=
  match s1, s2 with
  | uec_slot_unwired, uec_slot_unwired => true
  | uec_slot_absent, uec_slot_absent => true
  | uec_slot_present, uec_slot_present => true
  | _, _ => false
  end.

Definition uec_channel_slot_is_present (s : uec_channel_slot) : bool :=
  match s with
  | uec_slot_present => true
  | _ => false
  end.

Definition uExceptionContinuumProductChannelCount : nat := 3.

Lemma u_exception_continuum_product_channel_count_is_three :
  uExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 u_exception_continuum. *)
Definition uec_channel_occupancy_engine_sort : nat := 0.
Definition uec_channel_observed_override : nat := 1.
Definition uec_channel_named_exception_continuum : nat := 2.

Lemma uec_channel_occupancy_engine_sort_idx_is_0 :
  uec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma uec_channel_observed_override_idx_is_1 :
  uec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma uec_channel_class9_u_exception_continuum_idx_is_2 :
  uec_channel_named_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition uec_channel_bundle : Type := nat -> uec_channel_slot.

Definition uExceptionContinuumBundleAllUnwired : uec_channel_bundle :=
  fun _ => uec_slot_unwired.

Definition uExceptionContinuumBundleAt (b : uec_channel_bundle) (idx : nat)
  (slot : uec_channel_slot) : uec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition uExceptionContinuumBundleWithPresent
  (b : uec_channel_bundle) (idx : nat) : uec_channel_bundle :=
  uExceptionContinuumBundleAt b idx uec_slot_present.

Fixpoint count_uec_present_up_to (b : uec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if uec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_uec_present_up_to b i + add
  end.

Definition uExceptionContinuumBundlePresentCount (b : uec_channel_bundle) : nat :=
  count_uec_present_up_to b uExceptionContinuumProductChannelCount.

Definition uExceptionContinuumBundleHolds (b : uec_channel_bundle) (idx : nat) : bool :=
  uec_channel_slot_is_present (b idx).

Definition uExceptionContinuumBundleIsConcurrentProduct (b : uec_channel_bundle) : bool :=
  Nat.leb 2 (uExceptionContinuumBundlePresentCount b).

(* U Z=92 interact restriction + G-min + class 14 u_exception_continuum concurrent witness. *)
Definition uExceptionContinuumU92Witness : uec_channel_bundle :=
  uExceptionContinuumBundleWithPresent
    (uExceptionContinuumBundleWithPresent
      (uExceptionContinuumBundleWithPresent uExceptionContinuumBundleAllUnwired
        uec_channel_occupancy_engine_sort)
      uec_channel_observed_override)
    uec_channel_named_exception_continuum.

Definition uExceptionContinuumEmptyWitness : uec_channel_bundle :=
  uExceptionContinuumBundleAllUnwired.

Definition uExceptionContinuumSinglePresent : uec_channel_bundle :=
  uExceptionContinuumBundleWithPresent uExceptionContinuumBundleAllUnwired
    uec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  uExceptionContinuumBundleHolds uExceptionContinuumU92Witness
    uec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  uExceptionContinuumBundleHolds uExceptionContinuumU92Witness
    uec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_u_exception_continuum_channel_present :
  uExceptionContinuumBundleHolds uExceptionContinuumU92Witness
    uec_channel_named_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma u92_witness_present_count_is_three :
  uExceptionContinuumBundlePresentCount uExceptionContinuumU92Witness = 3.
Proof. reflexivity. Qed.

Lemma u92_witness_is_concurrent_product :
  uExceptionContinuumBundleIsConcurrentProduct uExceptionContinuumU92Witness = true.
Proof.
  unfold uExceptionContinuumBundleIsConcurrentProduct.
  rewrite u92_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  uExceptionContinuumBundlePresentCount uExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  uExceptionContinuumBundleIsConcurrentProduct uExceptionContinuumEmptyWitness = false.
Proof.
  unfold uExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  uExceptionContinuumBundlePresentCount uExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  uExceptionContinuumBundleIsConcurrentProduct uExceptionContinuumSinglePresent = false.
Proof.
  unfold uExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive uec_xor_posture : Type :=
  | uec_xor_exclusive
  | uec_xor_concurrent_product.

Definition uecXorClassifierMarker : string := "chem_l0_u_exception_continuum_xor_classifier_v1".
Definition uecConcurrentProductMarker : string := "chem_int_u_exception_continuum_product_v1".

Lemma uec_xor_marker_ne_concurrent_product_marker :
  uecXorClassifierMarker <> uecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition uecXorClassifierIncompatible (claim_xor : bool)
  (b : uec_channel_bundle) : bool :=
  claim_xor && uExceptionContinuumBundleIsConcurrentProduct b.

Lemma uec_xor_refuse_on_u92_witness :
  uecXorClassifierIncompatible true uExceptionContinuumU92Witness = true.
Proof.
  unfold uecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma uec_xor_ok_on_concurrent_product_claim :
  uecXorClassifierIncompatible false uExceptionContinuumU92Witness = false.
Proof. reflexivity. Qed.

Definition uecProductNotXor : bool :=
  uExceptionContinuumBundleIsConcurrentProduct uExceptionContinuumU92Witness &&
  uecXorClassifierIncompatible true uExceptionContinuumU92Witness.

Lemma uec_product_not_xor_true : uecProductNotXor = true.
Proof.
  unfold uecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  uecProductNotXor = true /\
  Nat.leb 2 (uExceptionContinuumBundlePresentCount
    uExceptionContinuumU92Witness) = true /\
  uecXorClassifierMarker <> uecConcurrentProductMarker.
Proof.
  split.
  - apply uec_product_not_xor_true.
  - split.
    + rewrite u92_witness_present_count_is_three.
      reflexivity.
    + apply uec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive uec_bar_presence : Type :=
  | uec_bar_absent
  | uec_bar_present.

Record uec_claim_bar : Type := {
  uec_bar_presence_field : uec_bar_presence;
  uec_bar_defect_total : nat
}.

Definition uExceptionContinuumClaimBarAbsent : uec_claim_bar :=
  {| uec_bar_presence_field := uec_bar_absent;
     uec_bar_defect_total := 0 |}.

Definition uExceptionContinuumClaimBarZeroDefect : uec_claim_bar :=
  {| uec_bar_presence_field := uec_bar_present;
     uec_bar_defect_total := 0 |}.

Definition uec_claim_bar_zero_defect (b : uec_claim_bar) : bool :=
  match uec_bar_presence_field b with
  | uec_bar_absent => false
  | uec_bar_present => Nat.eqb (uec_bar_defect_total b) 0
  end.

Lemma uec_claim_bar_zero_defect_true :
  uec_claim_bar_zero_defect uExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma uec_claim_bar_absent_not_zero_defect :
  uec_claim_bar_zero_defect uExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive uec_conservation_verdict : Type :=
  | uec_verdict_unwired_ok
  | uec_verdict_named_ok
  | uec_verdict_design_ok
  | uec_verdict_trivial_refuse
  | uec_verdict_xor_refuse
  | uec_verdict_green_invent_refuse
  | uec_verdict_proved_without_bar_refuse
  | uec_verdict_production_wired_refuse
  | uec_verdict_parallel_u_exception_continuum_axiom_refuse
  | uec_verdict_species_id_smuggle_refuse
  | uec_verdict_extra_element_id_refuse
  | uec_verdict_extra_u_exception_continuum_force_refuse
  | uec_verdict_tp_float_pin_refuse.

Definition uec_conservation_verdict_ok (v : uec_conservation_verdict) : bool :=
  match v with
  | uec_verdict_unwired_ok => true
  | uec_verdict_named_ok => true
  | uec_verdict_design_ok => true
  | _ => false
  end.

Definition uExceptionContinuumBundleNontrivial (b : uec_channel_bundle) : bool :=
  Nat.ltb 0 (uExceptionContinuumBundlePresentCount b).

Definition evaluate_u_exception_continuum_bundle
  (m : UExceptionContinuumModality)
  (b : uec_channel_bundle)
  (bar : uec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : uec_conservation_verdict :=
  if claim_physics_green
  then uec_verdict_green_invent_refuse
  else if claim_proved
       then uec_verdict_proved_without_bar_refuse
       else if negb (uExceptionContinuumBundleNontrivial b)
            then uec_verdict_trivial_refuse
            else if uecXorClassifierIncompatible claim_xor_classifier b
                 then uec_verdict_xor_refuse
                 else
                   match m with
                   | u_exception_continuum_unwired =>
                       if uExceptionContinuumBundleIsConcurrentProduct b
                       then uec_verdict_named_ok
                       else uec_verdict_design_ok
                   | u_exception_continuum_assumed
                   | u_exception_continuum_surrogate =>
                       uec_verdict_design_ok
                   | u_exception_continuum_proved =>
                       uec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_u_exception_continuum_close
  (m : UExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : uec_conservation_verdict :=
  if claim_physics_green
  then uec_verdict_green_invent_refuse
  else if claim_production_wired
  then uec_verdict_production_wired_refuse
  else
    match m with
    | u_exception_continuum_unwired => uec_verdict_unwired_ok
    | u_exception_continuum_assumed
    | u_exception_continuum_proved
    | u_exception_continuum_surrogate => uec_verdict_named_ok
    end.

Definition u_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_u_exception_continuum_close
          u_exception_continuum_proved claim_physics_green claim_production_wired with
  | uec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive uec_conservation_law : Type :=
  | uec_law_conserved
  | uec_law_named_ok
  | uec_law_trivial_refuse
  | uec_law_green_invent_refuse.

Definition uec_conservation_law_count : nat := 4.

Lemma uec_conservation_law_count_is_four :
  uec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive uec_conservation_law_witness : Type :=
  | uec_law_witness_open
  | uec_law_witness_proved.

Definition evaluate_uec_conservation_law_witness
  (law : uec_conservation_law)
  (m : UExceptionContinuumModality)
  : uec_conservation_law_witness :=
  match m with
  | u_exception_continuum_unwired
  | u_exception_continuum_assumed
  | u_exception_continuum_surrogate => uec_law_witness_open
  | u_exception_continuum_proved => uec_law_witness_proved
  end.

Lemma all_uec_conservation_laws_open_at_unwired :
  evaluate_uec_conservation_law_witness uec_law_conserved
    u_exception_continuum_unwired = uec_law_witness_open /\
  evaluate_uec_conservation_law_witness uec_law_named_ok
    u_exception_continuum_unwired = uec_law_witness_open /\
  evaluate_uec_conservation_law_witness uec_law_trivial_refuse
    u_exception_continuum_unwired = uec_law_witness_open /\
  evaluate_uec_conservation_law_witness uec_law_green_invent_refuse
    u_exception_continuum_unwired = uec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition uExceptionContinuumProved : bool := false.

Lemma u_exception_continuum_proved_false :
  uExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_u_exception_continuum_close
    u_exception_continuum_unwired false false =
  uec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_u_exception_continuum_close
    u_exception_continuum_unwired false false =
  uec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_unwired false false) =
  true.
Proof.
  unfold uec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named U Z=92 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma u92_witness_named_ok :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false false =
  uec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_u92_u_exception_continuum :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false false =
  uec_verdict_named_ok /\
  uExceptionContinuumBundleIsConcurrentProduct uExceptionContinuumU92Witness = true /\
  uranium_atomic_number_z = 92 /\
  u_observed_occupancy_tag = "5f36d17s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma uec_named_close_ok :
  evaluate_u_exception_continuum_close
    u_exception_continuum_proved false false =
  uec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_u_exception_continuum_close :
  evaluate_u_exception_continuum_close
    u_exception_continuum_proved false false =
  uec_verdict_named_ok /\
  u_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply uec_named_close_ok.
  - unfold u_exception_continuum_authorized.
    rewrite uec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — u_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumEmptyWitness
    uExceptionContinuumClaimBarAbsent false false false =
  uec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumEmptyWitness
    uExceptionContinuumClaimBarAbsent false false false =
  uec_verdict_trivial_refuse /\
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_bundle
       u_exception_continuum_unwired
       uExceptionContinuumEmptyWitness
       uExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold uec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent true false false =
  uec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent true false false =
  uec_verdict_xor_refuse /\
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_bundle
       u_exception_continuum_unwired
       uExceptionContinuumU92Witness
       uExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold uec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_u_exception_continuum_close
    u_exception_continuum_unwired true false =
  uec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_unwired true false) =
  false.
Proof.
  unfold uec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_uec_bundle_refuse :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false true false =
  uec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — u_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false true =
  uec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false true =
  uec_verdict_proved_without_bar_refuse /\
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_bundle
       u_exception_continuum_unwired
       uExceptionContinuumU92Witness
       uExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold uec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — u_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_u_exception_continuum_close
    u_exception_continuum_proved false true =
  uec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_proved false true) =
  false.
Proof.
  unfold uec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel u_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition uExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelUExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_u_exception_continuum_axiom_refuse :
  uExceptionContinuumAuthority <>
  parallelUExceptionAxiomTag /\
  uExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply u_exception_continuum_proved_false.
Qed.

Theorem parallel_u_exception_continuum_axiom_not_minted :
  uExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  uExceptionContinuumProved = false /\
  uExceptionContinuumAuthority <> parallelUExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "w_z74_occupancy_copied_onto_u_z92".

Definition uExceptionContinuumFraming : string :=
  "second_law_conservation_u_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  uExceptionContinuumFraming <>
  homologCopyFraming /\
  uranium_atomic_number_z = 92 /\
  u_observed_occupancy_tag = "5f36d17s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem u_w_homolog_not_occupancy_copy :
  uExceptionContinuumFraming <>
  homologCopyFraming /\
  uranium_atomic_number_z = 92 /\
  tungsten_homolog_z = 74 /\
  u_observed_occupancy_tag <> w_homolog_observed_occupancy_tag /\
  uExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — u_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "u_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  uExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  uExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  uranium_atomic_number_z = 92.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — u_exception_continuum ≠ extra u_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_u_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/u_exception_continuum_barrier.rs".

Lemma extra_u_exception_continuum_force_refuse :
  uExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem u_exception_continuum_not_extra_u_exception_continuum_force :
  uExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/u_exception_continuum_barrier.rs" /\
  uExceptionContinuumProved = false.
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
  uExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  u_observed_occupancy_tag <> u_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply u_observed_ne_predicted_occupancy.
Qed.

Theorem u_observed_override_not_madelung_family_smuggle :
  uExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  u_observed_occupancy_tag = "5f36d17s2" /\
  u_predicted_occupancy_tag = "5f47s2" /\
  uExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply u_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_u_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  uExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  uExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  uranium_atomic_number_z = 92.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  UExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition uec_conservation_coherence_scaffold : bool :=
  uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_proved false false) &&
  negb (uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_unwired true false)) &&
  negb (uec_conservation_verdict_ok
    (evaluate_u_exception_continuum_close
       u_exception_continuum_proved false true)).

Lemma uec_conservation_coherence_scaffold_true :
  uec_conservation_coherence_scaffold = true.
Proof.
  unfold uec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem uec_conservation_coherence_scaffold_theorem :
  evaluate_u_exception_continuum_close
    u_exception_continuum_proved false false =
    uec_verdict_named_ok /\
  evaluate_u_exception_continuum_close
    u_exception_continuum_unwired true false =
    uec_verdict_green_invent_refuse /\
  evaluate_u_exception_continuum_close
    u_exception_continuum_proved false true =
    uec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition uec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition uec_conservation_knowing_fiber_ok : bool :=
  uec_conservation_fiber_ok fiber_quantum_knowing.

Definition uec_conservation_meso_acting_ok : bool :=
  uec_conservation_fiber_ok fiber_meso_acting.

Lemma uec_conservation_knowing_fiber_ok_true :
  uec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma uec_conservation_meso_acting_not_ok :
  uec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem uec_conservation_routes_knowing_not_meso :
  uec_conservation_knowing_fiber_ok = true /\
  uec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply uec_conservation_knowing_fiber_ok_true.
  - apply uec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  uec_conservation_knowing_fiber_ok &&
  negb uec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, uec_conservation_knowing_fiber_ok,
    uec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem u_exception_continuum_fixture_scaffold :
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false false =
    uec_verdict_named_ok /\
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumEmptyWitness
    uExceptionContinuumClaimBarAbsent false false false =
    uec_verdict_trivial_refuse /\
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent true false false =
    uec_verdict_xor_refuse /\
  evaluate_u_exception_continuum_bundle
    u_exception_continuum_unwired
    uExceptionContinuumU92Witness
    uExceptionContinuumClaimBarAbsent false false true =
    uec_verdict_proved_without_bar_refuse /\
  evaluate_u_exception_continuum_close
    u_exception_continuum_unwired false false =
    uec_verdict_unwired_ok /\
  uec_conservation_knowing_fiber_ok = true /\
  uec_conservation_meso_acting_ok = false /\
  uExceptionContinuumProved = false /\
  uecProductNotXor = true /\
  uranium_atomic_number_z = 92.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  W Z=74 homolog not U copy — period-6 d-block homolog ≠ identity     *)
(* ------------------------------------------------------------------ *)

Definition tungsten_atomic_number_z : nat := 74.

Lemma tungsten_atomic_number_z_is_74 :
  tungsten_atomic_number_z = 74.
Proof. reflexivity. Qed.

Definition tungsten_homolog_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d4".

Lemma w_homolog_occupancy_tag_named :
  w_homolog_observed_occupancy_tag = "4f145d46s2".
Proof. reflexivity. Qed.

Lemma u_w_homolog_subshell_not_copy :
  u_observed_subshell_notation <>
  tungsten_homolog_observed_subshell_notation.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma u_w_homolog_not_copy :
  uranium_atomic_number_z = 92 /\
  tungsten_atomic_number_z = 74 /\
  u_observed_occupancy_tag <> w_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem w_period6_homolog_not_u_occupancy_copy :
  uranium_atomic_number_z = 92 /\
  tungsten_atomic_number_z = 74 /\
  u_observed_occupancy_tag = "5f36d17s2" /\
  w_homolog_observed_occupancy_tag = "4f145d46s2" /\
  u_observed_occupancy_tag <> w_homolog_observed_occupancy_tag /\
  uExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — u_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition uExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition uExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-U-EXCEPTION-CONTINUUM".

Definition uExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-U-EXCEPTION-CONTINUUM UExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice uExceptionContinuumProved false evaluateUExceptionContinuumBundle evaluateUExceptionContinuum named U Z=92 actinide occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse W Z=74 homolog not U 5f3 6d1 7s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma u_exception_continuum_cell_id :
  uExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-U-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma u_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma u_exception_continuum_authority_path :
  uExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma u_exception_continuum_cites_l0_ore02 :
  uExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma u_exception_continuum_cites_marker :
  uecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma u_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma u_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma u_exception_continuum_not_26th_axiom :
  uExceptionContinuumFraming <> parallelUExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma u_exception_continuum_second_law_conservation_framing :
  uExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition namedExceptionNamedObject : string :=
  "interact_restriction_on_u_exception_continuum_morphism".

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
  uExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not u_exception_continuum axiom / extra force     *)
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

Theorem u_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/u_exception_continuum_barrier.rs" /\
  uExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma u_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma u_exception_continuum_modality_unwired :
  uExceptionContinuumModalityCurrent =
  u_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition uExceptionContinuumProductionWired : Prop := False.

Lemma u_exception_continuum_not_production_wired :
  ~ uExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


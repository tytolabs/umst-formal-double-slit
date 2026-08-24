(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CuExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Cu Z=29 d-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Cu 3d10 4s1 d-block Madelung exception; Ag Z=47 homolog not Cu copy. *)
(*  cuExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **cu_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive CuExceptionContinuumModality : Type :=
  | cu_exception_continuum_unwired
  | cu_exception_continuum_assumed
  | cu_exception_continuum_proved
  | cu_exception_continuum_surrogate.

Definition cuExceptionContinuumModalityCurrent :
  CuExceptionContinuumModality :=
  cu_exception_continuum_unwired.

Definition cu_exception_continuum_lattice_cardinality : nat := 4.

Lemma cu_exception_continuum_lattice_cardinality_is_four :
  cu_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma cu_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb cu_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold cu_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — cu_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_cu_exception_continuum_idx : nat := 14.

Lemma pattern_class_cu_exception_continuum_idx_is_14 :
  pattern_class_cu_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma cu_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_cu_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_cu_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_cu_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_cu_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_cu_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_cu_exception_continuum_tag_nonempty :
  pattern_class_cu_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_cu_exception_continuum_tag_nonempty :
  north_star_class_14_cu_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Cu Z=29 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition copper_atomic_number_z : nat := 29.

Lemma copper_atomic_number_z_is_29 :
  copper_atomic_number_z = 29.
Proof. reflexivity. Qed.

Definition copper_z_valid : bool :=
  Nat.ltb 0 copper_atomic_number_z &&
  Nat.leb copper_atomic_number_z iupac_table_cardinality.

Lemma copper_z_valid_true : copper_z_valid = true.
Proof.
  unfold copper_z_valid, copper_atomic_number_z, iupac_table_cardinality.
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

Definition cu_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma cu_exception_continuum_factor_tag_nonempty :
  cu_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive cuec_channel_slot : Type :=
  | cuec_slot_unwired
  | cuec_slot_absent
  | cuec_slot_present.

Definition cuec_channel_slot_beq (s1 s2 : cuec_channel_slot) : bool :=
  match s1, s2 with
  | cuec_slot_unwired, cuec_slot_unwired => true
  | cuec_slot_absent, cuec_slot_absent => true
  | cuec_slot_present, cuec_slot_present => true
  | _, _ => false
  end.

Definition cuec_channel_slot_is_present (s : cuec_channel_slot) : bool :=
  match s with
  | cuec_slot_present => true
  | _ => false
  end.

Definition cuExceptionContinuumProductChannelCount : nat := 3.

Lemma cu_exception_continuum_product_channel_count_is_three :
  cuExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 cu_exception_continuum. *)
Definition cuec_channel_occupancy_engine_sort : nat := 0.
Definition cuec_channel_observed_override : nat := 1.
Definition cuec_channel_dblock_exception_continuum : nat := 2.

Lemma cuec_channel_occupancy_engine_sort_idx_is_0 :
  cuec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma cuec_channel_observed_override_idx_is_1 :
  cuec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma cuec_channel_class9_cu_exception_continuum_idx_is_2 :
  cuec_channel_dblock_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition cuec_channel_bundle : Type := nat -> cuec_channel_slot.

Definition cuExceptionContinuumBundleAllUnwired : cuec_channel_bundle :=
  fun _ => cuec_slot_unwired.

Definition cuExceptionContinuumBundleAt (b : cuec_channel_bundle) (idx : nat)
  (slot : cuec_channel_slot) : cuec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition cuExceptionContinuumBundleWithPresent
  (b : cuec_channel_bundle) (idx : nat) : cuec_channel_bundle :=
  cuExceptionContinuumBundleAt b idx cuec_slot_present.

Fixpoint count_cuec_present_up_to (b : cuec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if cuec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_cuec_present_up_to b i + add
  end.

Definition cuExceptionContinuumBundlePresentCount (b : cuec_channel_bundle) : nat :=
  count_cuec_present_up_to b cuExceptionContinuumProductChannelCount.

Definition cuExceptionContinuumBundleHolds (b : cuec_channel_bundle) (idx : nat) : bool :=
  cuec_channel_slot_is_present (b idx).

Definition cuExceptionContinuumBundleIsConcurrentProduct (b : cuec_channel_bundle) : bool :=
  Nat.leb 2 (cuExceptionContinuumBundlePresentCount b).

(* Cu Z=29 interact restriction + G-min + class 14 cu_exception_continuum concurrent witness. *)
Definition cuExceptionContinuumCu29Witness : cuec_channel_bundle :=
  cuExceptionContinuumBundleWithPresent
    (cuExceptionContinuumBundleWithPresent
      (cuExceptionContinuumBundleWithPresent cuExceptionContinuumBundleAllUnwired
        cuec_channel_occupancy_engine_sort)
      cuec_channel_observed_override)
    cuec_channel_dblock_exception_continuum.

Definition cuExceptionContinuumEmptyWitness : cuec_channel_bundle :=
  cuExceptionContinuumBundleAllUnwired.

Definition cuExceptionContinuumSinglePresent : cuec_channel_bundle :=
  cuExceptionContinuumBundleWithPresent cuExceptionContinuumBundleAllUnwired
    cuec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  cuExceptionContinuumBundleHolds cuExceptionContinuumCu29Witness
    cuec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  cuExceptionContinuumBundleHolds cuExceptionContinuumCu29Witness
    cuec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_cu_exception_continuum_channel_present :
  cuExceptionContinuumBundleHolds cuExceptionContinuumCu29Witness
    cuec_channel_dblock_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma cu29_witness_present_count_is_three :
  cuExceptionContinuumBundlePresentCount cuExceptionContinuumCu29Witness = 3.
Proof. reflexivity. Qed.

Lemma cu29_witness_is_concurrent_product :
  cuExceptionContinuumBundleIsConcurrentProduct cuExceptionContinuumCu29Witness = true.
Proof.
  unfold cuExceptionContinuumBundleIsConcurrentProduct.
  rewrite cu29_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  cuExceptionContinuumBundlePresentCount cuExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  cuExceptionContinuumBundleIsConcurrentProduct cuExceptionContinuumEmptyWitness = false.
Proof.
  unfold cuExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  cuExceptionContinuumBundlePresentCount cuExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  cuExceptionContinuumBundleIsConcurrentProduct cuExceptionContinuumSinglePresent = false.
Proof.
  unfold cuExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive cuec_xor_posture : Type :=
  | cuec_xor_exclusive
  | cuec_xor_concurrent_product.

Definition cuecXorClassifierMarker : string := "chem_l0_cu_exception_continuum_xor_classifier_v1".
Definition cuecConcurrentProductMarker : string := "chem_int_cu_exception_continuum_product_v1".

Lemma cuec_xor_marker_ne_concurrent_product_marker :
  cuecXorClassifierMarker <> cuecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition cuecXorClassifierIncompatible (claim_xor : bool)
  (b : cuec_channel_bundle) : bool :=
  claim_xor && cuExceptionContinuumBundleIsConcurrentProduct b.

Lemma cuec_xor_refuse_on_cu29_witness :
  cuecXorClassifierIncompatible true cuExceptionContinuumCu29Witness = true.
Proof.
  unfold cuecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma cuec_xor_ok_on_concurrent_product_claim :
  cuecXorClassifierIncompatible false cuExceptionContinuumCu29Witness = false.
Proof. reflexivity. Qed.

Definition cuecProductNotXor : bool :=
  cuExceptionContinuumBundleIsConcurrentProduct cuExceptionContinuumCu29Witness &&
  cuecXorClassifierIncompatible true cuExceptionContinuumCu29Witness.

Lemma cuec_product_not_xor_true : cuecProductNotXor = true.
Proof.
  unfold cuecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  cuecProductNotXor = true /\
  Nat.leb 2 (cuExceptionContinuumBundlePresentCount
    cuExceptionContinuumCu29Witness) = true /\
  cuecXorClassifierMarker <> cuecConcurrentProductMarker.
Proof.
  split.
  - apply cuec_product_not_xor_true.
  - split.
    + rewrite cu29_witness_present_count_is_three.
      reflexivity.
    + apply cuec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive cuec_bar_presence : Type :=
  | cuec_bar_absent
  | cuec_bar_present.

Record cuec_claim_bar : Type := {
  cuec_bar_presence_field : cuec_bar_presence;
  cuec_bar_defect_total : nat
}.

Definition cuExceptionContinuumClaimBarAbsent : cuec_claim_bar :=
  {| cuec_bar_presence_field := cuec_bar_absent;
     cuec_bar_defect_total := 0 |}.

Definition cuExceptionContinuumClaimBarZeroDefect : cuec_claim_bar :=
  {| cuec_bar_presence_field := cuec_bar_present;
     cuec_bar_defect_total := 0 |}.

Definition cuec_claim_bar_zero_defect (b : cuec_claim_bar) : bool :=
  match cuec_bar_presence_field b with
  | cuec_bar_absent => false
  | cuec_bar_present => Nat.eqb (cuec_bar_defect_total b) 0
  end.

Lemma cuec_claim_bar_zero_defect_true :
  cuec_claim_bar_zero_defect cuExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma cuec_claim_bar_absent_not_zero_defect :
  cuec_claim_bar_zero_defect cuExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive cuec_conservation_verdict : Type :=
  | cuec_verdict_unwired_ok
  | cuec_verdict_named_ok
  | cuec_verdict_design_ok
  | cuec_verdict_trivial_refuse
  | cuec_verdict_xor_refuse
  | cuec_verdict_green_invent_refuse
  | cuec_verdict_proved_without_bar_refuse
  | cuec_verdict_production_wired_refuse
  | cuec_verdict_parallel_cu_exception_continuum_axiom_refuse
  | cuec_verdict_species_id_smuggle_refuse
  | cuec_verdict_extra_element_id_refuse
  | cuec_verdict_extra_cu_exception_continuum_force_refuse
  | cuec_verdict_tp_float_pin_refuse.

Definition cuec_conservation_verdict_ok (v : cuec_conservation_verdict) : bool :=
  match v with
  | cuec_verdict_unwired_ok => true
  | cuec_verdict_named_ok => true
  | cuec_verdict_design_ok => true
  | _ => false
  end.

Definition cuExceptionContinuumBundleNontrivial (b : cuec_channel_bundle) : bool :=
  Nat.ltb 0 (cuExceptionContinuumBundlePresentCount b).

Definition evaluate_cu_exception_continuum_bundle
  (m : CuExceptionContinuumModality)
  (b : cuec_channel_bundle)
  (bar : cuec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : cuec_conservation_verdict :=
  if claim_physics_green
  then cuec_verdict_green_invent_refuse
  else if claim_proved
       then cuec_verdict_proved_without_bar_refuse
       else if negb (cuExceptionContinuumBundleNontrivial b)
            then cuec_verdict_trivial_refuse
            else if cuecXorClassifierIncompatible claim_xor_classifier b
                 then cuec_verdict_xor_refuse
                 else
                   match m with
                   | cu_exception_continuum_unwired =>
                       if cuExceptionContinuumBundleIsConcurrentProduct b
                       then cuec_verdict_named_ok
                       else cuec_verdict_design_ok
                   | cu_exception_continuum_assumed
                   | cu_exception_continuum_surrogate =>
                       cuec_verdict_design_ok
                   | cu_exception_continuum_proved =>
                       cuec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_cu_exception_continuum_close
  (m : CuExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : cuec_conservation_verdict :=
  if claim_physics_green
  then cuec_verdict_green_invent_refuse
  else if claim_production_wired
  then cuec_verdict_production_wired_refuse
  else
    match m with
    | cu_exception_continuum_unwired => cuec_verdict_unwired_ok
    | cu_exception_continuum_assumed
    | cu_exception_continuum_proved
    | cu_exception_continuum_surrogate => cuec_verdict_named_ok
    end.

Definition cu_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_cu_exception_continuum_close
          cu_exception_continuum_proved claim_physics_green claim_production_wired with
  | cuec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive cuec_conservation_law : Type :=
  | cuec_law_conserved
  | cuec_law_named_ok
  | cuec_law_trivial_refuse
  | cuec_law_green_invent_refuse.

Definition cuec_conservation_law_count : nat := 4.

Lemma cuec_conservation_law_count_is_four :
  cuec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive cuec_conservation_law_witness : Type :=
  | cuec_law_witness_open
  | cuec_law_witness_proved.

Definition evaluate_cuec_conservation_law_witness
  (law : cuec_conservation_law)
  (m : CuExceptionContinuumModality)
  : cuec_conservation_law_witness :=
  match m with
  | cu_exception_continuum_unwired
  | cu_exception_continuum_assumed
  | cu_exception_continuum_surrogate => cuec_law_witness_open
  | cu_exception_continuum_proved => cuec_law_witness_proved
  end.

Lemma all_cuec_conservation_laws_open_at_unwired :
  evaluate_cuec_conservation_law_witness cuec_law_conserved
    cu_exception_continuum_unwired = cuec_law_witness_open /\
  evaluate_cuec_conservation_law_witness cuec_law_named_ok
    cu_exception_continuum_unwired = cuec_law_witness_open /\
  evaluate_cuec_conservation_law_witness cuec_law_trivial_refuse
    cu_exception_continuum_unwired = cuec_law_witness_open /\
  evaluate_cuec_conservation_law_witness cuec_law_green_invent_refuse
    cu_exception_continuum_unwired = cuec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition cuExceptionContinuumProved : bool := false.

Lemma cu_exception_continuum_proved_false :
  cuExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_unwired false false =
  cuec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_unwired false false =
  cuec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_unwired false false) =
  true.
Proof.
  unfold cuec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Cu Z=29 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma cu29_witness_named_ok :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false false =
  cuec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cu29_cu_exception_continuum :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false false =
  cuec_verdict_named_ok /\
  cuExceptionContinuumBundleIsConcurrentProduct cuExceptionContinuumCu29Witness = true /\
  copper_atomic_number_z = 29 /\
  pattern_class_cu_exception_continuum_idx = 14.
Proof.
  repeat split; reflexivity.
Qed.

Lemma cuec_named_close_ok :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_proved false false =
  cuec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cu_exception_continuum_close :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_proved false false =
  cuec_verdict_named_ok /\
  cu_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply cuec_named_close_ok.
  - unfold cu_exception_continuum_authorized.
    rewrite cuec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — cu_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumEmptyWitness
    cuExceptionContinuumClaimBarAbsent false false false =
  cuec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumEmptyWitness
    cuExceptionContinuumClaimBarAbsent false false false =
  cuec_verdict_trivial_refuse /\
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_bundle
       cu_exception_continuum_unwired
       cuExceptionContinuumEmptyWitness
       cuExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold cuec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent true false false =
  cuec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent true false false =
  cuec_verdict_xor_refuse /\
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_bundle
       cu_exception_continuum_unwired
       cuExceptionContinuumCu29Witness
       cuExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold cuec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_unwired true false =
  cuec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_unwired true false) =
  false.
Proof.
  unfold cuec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_cuec_bundle_refuse :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false true false =
  cuec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — cu_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false true =
  cuec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false true =
  cuec_verdict_proved_without_bar_refuse /\
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_bundle
       cu_exception_continuum_unwired
       cuExceptionContinuumCu29Witness
       cuExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold cuec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — cu_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_proved false true =
  cuec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_proved false true) =
  false.
Proof.
  unfold cuec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel cu_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition cuExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelCuExceptionAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_cu_exception_continuum_axiom_refuse :
  cuExceptionContinuumAuthority <>
  parallelCuExceptionAxiomTag /\
  cuExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply cu_exception_continuum_proved_false.
Qed.

Theorem parallel_cu_exception_continuum_axiom_not_minted :
  cuExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  cuExceptionContinuumProved = false /\
  cuExceptionContinuumAuthority <> parallelCuExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopySmuggleFraming : string :=
  "homolog_subshell_copy_not_named_object".

Definition cuExceptionContinuumFraming : string :=
  "second_law_conservation_cu_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  cuExceptionContinuumFraming <>
  homologCopySmuggleFraming /\
  copper_atomic_number_z = 29 /\
  pattern_class_cu_exception_continuum_idx = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem occupancy_engine_sort_not_homolog_copy_smuggle :
  cuExceptionContinuumFraming <>
  homologCopySmuggleFraming /\
  copper_atomic_number_z = 29 /\
  pattern_class_cu_exception_continuum_idx = 14 /\
  cuExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — cu_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "homolog_occupancy_subshell_copy_smuggle".

Lemma extra_element_id_refuse :
  cuExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  cuExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  copper_atomic_number_z = 29.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — cu_exception_continuum ≠ extra cu_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_cu_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/cu_exception_continuum_barrier.rs".

Lemma extra_cu_exception_continuum_force_refuse :
  cuExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem cu_exception_continuum_not_extra_cu_exception_continuum_force :
  cuExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/cu_exception_continuum_barrier.rs" /\
  cuExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_cu_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  cuExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  cuExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  copper_atomic_number_z = 29.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  CuExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition cuec_conservation_coherence_scaffold : bool :=
  cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_proved false false) &&
  negb (cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_unwired true false)) &&
  negb (cuec_conservation_verdict_ok
    (evaluate_cu_exception_continuum_close
       cu_exception_continuum_proved false true)).

Lemma cuec_conservation_coherence_scaffold_true :
  cuec_conservation_coherence_scaffold = true.
Proof.
  unfold cuec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cuec_conservation_coherence_scaffold_theorem :
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_proved false false =
    cuec_verdict_named_ok /\
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_unwired true false =
    cuec_verdict_green_invent_refuse /\
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_proved false true =
    cuec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition cuec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition cuec_conservation_knowing_fiber_ok : bool :=
  cuec_conservation_fiber_ok fiber_quantum_knowing.

Definition cuec_conservation_meso_acting_ok : bool :=
  cuec_conservation_fiber_ok fiber_meso_acting.

Lemma cuec_conservation_knowing_fiber_ok_true :
  cuec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma cuec_conservation_meso_acting_not_ok :
  cuec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem cuec_conservation_routes_knowing_not_meso :
  cuec_conservation_knowing_fiber_ok = true /\
  cuec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply cuec_conservation_knowing_fiber_ok_true.
  - apply cuec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  cuec_conservation_knowing_fiber_ok &&
  negb cuec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, cuec_conservation_knowing_fiber_ok,
    cuec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem cu_exception_continuum_fixture_scaffold :
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false false =
    cuec_verdict_named_ok /\
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumEmptyWitness
    cuExceptionContinuumClaimBarAbsent false false false =
    cuec_verdict_trivial_refuse /\
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent true false false =
    cuec_verdict_xor_refuse /\
  evaluate_cu_exception_continuum_bundle
    cu_exception_continuum_unwired
    cuExceptionContinuumCu29Witness
    cuExceptionContinuumClaimBarAbsent false false true =
    cuec_verdict_proved_without_bar_refuse /\
  evaluate_cu_exception_continuum_close
    cu_exception_continuum_unwired false false =
    cuec_verdict_unwired_ok /\
  cuec_conservation_knowing_fiber_ok = true /\
  cuec_conservation_meso_acting_ok = false /\
  cuExceptionContinuumProved = false /\
  cuecProductNotXor = true /\
  copper_atomic_number_z = 29.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ag Z=47 homolog not Cu copy — period-5 group-11 homolog ≠ identity  *)
(* ------------------------------------------------------------------ *)

Definition silver_atomic_number_z : nat := 47.

Lemma silver_atomic_number_z_is_47 :
  silver_atomic_number_z = 47.
Proof. reflexivity. Qed.

Definition copper_occupancy_tag : string := "3d104s1".

Definition silver_occupancy_tag : string := "4d105s1".

Lemma copper_silver_occupancy_tags_distinct :
  copper_occupancy_tag <> silver_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma ag_cu_homolog_not_copy :
  copper_atomic_number_z = 29 /\
  silver_atomic_number_z = 47 /\
  copper_occupancy_tag <> silver_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ag_period5_homolog_not_cu_occupancy_copy :
  copper_atomic_number_z = 29 /\
  silver_atomic_number_z = 47 /\
  copper_occupancy_tag = "3d104s1" /\
  silver_occupancy_tag = "4d105s1" /\
  copper_occupancy_tag <> silver_occupancy_tag /\
  cuExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — cu_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition cuExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition cuExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-CU-EXCEPTION-CONTINUUM".

Definition cuExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CU-EXCEPTION-CONTINUUM CuExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice cuExceptionContinuumProved false evaluateCuExceptionContinuumBundle evaluateCuExceptionContinuum named Cu Z=29 d-block occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ag Z=47 homolog not Cu 3d10 4s1 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma cu_exception_continuum_cell_id :
  cuExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-CU-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma cu_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma cu_exception_continuum_authority_path :
  cuExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma cu_exception_continuum_cites_l0_ore02 :
  cuExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma cu_exception_continuum_cites_marker :
  cuecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma cu_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma cu_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma cu_exception_continuum_not_26th_axiom :
  cuExceptionContinuumFraming <> parallelCuExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma cu_exception_continuum_second_law_conservation_framing :
  cuExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_cu_exception_continuum_morphism".

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
  cuExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not cu_exception_continuum axiom / extra force     *)
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

Theorem cu_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/cu_exception_continuum_barrier.rs" /\
  cuExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma cu_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma cu_exception_continuum_modality_unwired :
  cuExceptionContinuumModalityCurrent =
  cu_exception_continuum_unwired.
Proof. reflexivity. Qed.

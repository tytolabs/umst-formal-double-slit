(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AssayMeasurementLandauerConservation.v                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 21 **assay_measurement_landauer**         *)
(*  **conservation**. Measurement pays Landauer; floor ≠ CPU-heat /    *)
(*  wall-clock smuggle; not a parallel assay axiom. Concurrent Π_c      *)
(*  PatternBundle factor — **product** not XOR.                         *)
(*  assayMeasurementLandauerConservationProved false. Modality Unwired. *)
(*  WAVE100: not wired in lib.rs.                                       *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/assay_measurement_landauer.rs (cite).      *)
(*  INT: umst/umst-chem/src/l0_tables/assay_measurement_landauer.rs.   *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-21 **assay_measurement_landauer** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive AssayMeasurementLandauerConservationModality : Type :=
  | assay_measurement_landauer_conservation_unwired
  | assay_measurement_landauer_conservation_assumed
  | assay_measurement_landauer_conservation_proved
  | assay_measurement_landauer_conservation_surrogate.

Definition assayMeasurementLandauerConservationModalityCurrent :
  AssayMeasurementLandauerConservationModality :=
  assay_measurement_landauer_conservation_unwired.

Definition assay_measurement_landauer_lattice_cardinality : nat := 4.

Lemma assay_measurement_landauer_lattice_cardinality_is_four :
  assay_measurement_landauer_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma assay_measurement_landauer_lattice_not_118_squared :
  negb (Nat.eqb assay_measurement_landauer_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold assay_measurement_landauer_lattice_cardinality.
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

(* North-star §2 class 21 — assay_measurement_landauer concurrent Π_c factor. *)
Definition pattern_class_assay_idx : nat := 21.

Lemma pattern_class_assay_idx_is_21 :
  pattern_class_assay_idx = 21.
Proof. reflexivity. Qed.

Lemma assay_measurement_landauer_class_index_valid :
  pattern_class_index_valid pattern_class_assay_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_assay_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierAssayMeasurementLandauerRowId : string := "X21".

Lemma cross_classifier_assay_measurement_landauer_row_named :
  crossClassifierAssayMeasurementLandauerRowId = "X21".
Proof. reflexivity. Qed.

Definition pattern_class_assay_measurement_landauer_tag : string :=
  "assay_measurement_landauer".

Definition north_star_class_20_assay_measurement_landauer_tag : string :=
  "class 21 assay".

Lemma pattern_class_assay_measurement_landauer_tag_nonempty :
  pattern_class_assay_measurement_landauer_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_20_assay_measurement_landauer_tag_nonempty :
  north_star_class_20_assay_measurement_landauer_tag <> "".
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

Definition assay_measurement_landauer_factor_tag : string :=
  "assay_measurement_landauer".

Definition measurement_landauer_floor_channel_tag : string := "measurement_landauer_floor".

Definition cpu_heat_wall_clock_not_assay_channel_tag : string := "cpu_heat_wall_clock_not_assay".

Lemma assay_measurement_landauer_factor_tag_nonempty :
  assay_measurement_landauer_factor_tag <> "".
Proof. discriminate. Qed.

Lemma measurement_landauer_floor_channel_tag_nonempty :
  measurement_landauer_floor_channel_tag <> "".
Proof. discriminate. Qed.

Lemma cpu_heat_wall_clock_not_assay_channel_tag_nonempty :
  cpu_heat_wall_clock_not_assay_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive amlc_channel_slot : Type :=
  | amlc_slot_unwired
  | amlc_slot_absent
  | amlc_slot_present.

Definition amlc_channel_slot_beq (s1 s2 : amlc_channel_slot) : bool :=
  match s1, s2 with
  | amlc_slot_unwired, amlc_slot_unwired => true
  | amlc_slot_absent, amlc_slot_absent => true
  | amlc_slot_present, amlc_slot_present => true
  | _, _ => false
  end.

Definition amlc_channel_slot_is_present (s : amlc_channel_slot) : bool :=
  match s with
  | amlc_slot_present => true
  | _ => false
  end.

Definition assayMeasurementLandauerProductChannelCount : nat := 3.

Lemma assay_measurement_landauer_product_channel_count_is_three :
  assayMeasurementLandauerProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = measurement Landauer floor, 1 = CPU-heat wall-clock refuse, 2 = class 21 assay. *)
Definition amlc_channel_measurement_landauer_floor : nat := 0.
Definition amlc_channel_cpu_heat_wall_clock_not_assay : nat := 1.
Definition amlc_channel_class21_assay : nat := 2.

Lemma amlc_channel_measurement_landauer_floor_idx_is_0 :
  amlc_channel_measurement_landauer_floor = 0.
Proof. reflexivity. Qed.

Lemma amlc_channel_cpu_heat_wall_clock_not_assay_idx_is_1 :
  amlc_channel_cpu_heat_wall_clock_not_assay = 1.
Proof. reflexivity. Qed.

Lemma amlc_channel_class21_assay_measurement_landauer_idx_is_2 :
  amlc_channel_class21_assay = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition amlc_channel_bundle : Type := nat -> amlc_channel_slot.

Definition assayMeasurementLandauerBundleAllUnwired : amlc_channel_bundle :=
  fun _ => amlc_slot_unwired.

Definition assayMeasurementLandauerBundleAt (b : amlc_channel_bundle) (idx : nat)
  (slot : amlc_channel_slot) : amlc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition assayMeasurementLandauerBundleWithPresent
  (b : amlc_channel_bundle) (idx : nat) : amlc_channel_bundle :=
  assayMeasurementLandauerBundleAt b idx amlc_slot_present.

Fixpoint count_amlc_present_up_to (b : amlc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if amlc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_amlc_present_up_to b i + add
  end.

Definition assayMeasurementLandauerBundlePresentCount (b : amlc_channel_bundle) : nat :=
  count_amlc_present_up_to b assayMeasurementLandauerProductChannelCount.

Definition assayMeasurementLandauerBundleHolds (b : amlc_channel_bundle) (idx : nat) : bool :=
  amlc_channel_slot_is_present (b idx).

Definition assayMeasurementLandauerBundleIsConcurrentProduct (b : amlc_channel_bundle) : bool :=
  Nat.leb 2 (assayMeasurementLandauerBundlePresentCount b).

(* Au Z=79 measurement Landauer floor + CPU-heat wall-clock refuse + class 21 assay concurrent witness. *)
Definition assayMeasurementLandauerAu79Witness : amlc_channel_bundle :=
  assayMeasurementLandauerBundleWithPresent
    (assayMeasurementLandauerBundleWithPresent
      (assayMeasurementLandauerBundleWithPresent assayMeasurementLandauerBundleAllUnwired
        amlc_channel_measurement_landauer_floor)
      amlc_channel_cpu_heat_wall_clock_not_assay)
    amlc_channel_class21_assay.

Definition assayMeasurementLandauerEmptyWitness : amlc_channel_bundle :=
  assayMeasurementLandauerBundleAllUnwired.

Definition assayMeasurementLandauerSinglePresent : amlc_channel_bundle :=
  assayMeasurementLandauerBundleWithPresent assayMeasurementLandauerBundleAllUnwired
    amlc_channel_measurement_landauer_floor.

Lemma measurement_landauer_floor_channel_present :
  assayMeasurementLandauerBundleHolds assayMeasurementLandauerAu79Witness
    amlc_channel_measurement_landauer_floor = true.
Proof. reflexivity. Qed.

Lemma cpu_heat_wall_clock_not_assay_channel_present :
  assayMeasurementLandauerBundleHolds assayMeasurementLandauerAu79Witness
    amlc_channel_cpu_heat_wall_clock_not_assay = true.
Proof. reflexivity. Qed.

Lemma class21_assay_measurement_landauer_channel_present :
  assayMeasurementLandauerBundleHolds assayMeasurementLandauerAu79Witness
    amlc_channel_class21_assay = true.
Proof. reflexivity. Qed.

Lemma au79_witness_present_count_is_three :
  assayMeasurementLandauerBundlePresentCount assayMeasurementLandauerAu79Witness = 3.
Proof. reflexivity. Qed.

Lemma au79_witness_is_concurrent_product :
  assayMeasurementLandauerBundleIsConcurrentProduct assayMeasurementLandauerAu79Witness = true.
Proof.
  unfold assayMeasurementLandauerBundleIsConcurrentProduct.
  rewrite au79_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  assayMeasurementLandauerBundlePresentCount assayMeasurementLandauerEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  assayMeasurementLandauerBundleIsConcurrentProduct assayMeasurementLandauerEmptyWitness = false.
Proof.
  unfold assayMeasurementLandauerBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  assayMeasurementLandauerBundlePresentCount assayMeasurementLandauerSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  assayMeasurementLandauerBundleIsConcurrentProduct assayMeasurementLandauerSinglePresent = false.
Proof.
  unfold assayMeasurementLandauerBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive amlc_xor_posture : Type :=
  | amlc_xor_exclusive
  | amlc_xor_concurrent_product.

Definition amllXorClassifierMarker : string := "chem_l0_assay_measurement_landauer_xor_classifier_v1".
Definition amllConcurrentProductMarker : string := "chem_int_assay_measurement_landauer_product_v1".

Lemma amlc_xor_marker_ne_concurrent_product_marker :
  amllXorClassifierMarker <> amllConcurrentProductMarker.
Proof. discriminate. Qed.

Definition amllXorClassifierIncompatible (claim_xor : bool)
  (b : amlc_channel_bundle) : bool :=
  claim_xor && assayMeasurementLandauerBundleIsConcurrentProduct b.

Lemma amlc_xor_refuse_on_au79_witness :
  amllXorClassifierIncompatible true assayMeasurementLandauerAu79Witness = true.
Proof.
  unfold amllXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma amlc_xor_ok_on_concurrent_product_claim :
  amllXorClassifierIncompatible false assayMeasurementLandauerAu79Witness = false.
Proof. reflexivity. Qed.

Definition amllProductNotXor : bool :=
  assayMeasurementLandauerBundleIsConcurrentProduct assayMeasurementLandauerAu79Witness &&
  amllXorClassifierIncompatible true assayMeasurementLandauerAu79Witness.

Lemma amlc_product_not_xor_true : amllProductNotXor = true.
Proof.
  unfold amllProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  amllProductNotXor = true /\
  Nat.leb 2 (assayMeasurementLandauerBundlePresentCount
    assayMeasurementLandauerAu79Witness) = true /\
  amllXorClassifierMarker <> amllConcurrentProductMarker.
Proof.
  split.
  - apply amlc_product_not_xor_true.
  - split.
    + rewrite au79_witness_present_count_is_three.
      reflexivity.
    + apply amlc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive amlc_bar_presence : Type :=
  | amlc_bar_absent
  | amlc_bar_present.

Record amlc_claim_bar : Type := {
  amlc_bar_presence_field : amlc_bar_presence;
  amlc_bar_defect_total : nat
}.

Definition assay_measurement_landauerClaimBarAbsent : amlc_claim_bar :=
  {| amlc_bar_presence_field := amlc_bar_absent;
     amlc_bar_defect_total := 0 |}.

Definition assay_measurement_landauerClaimBarZeroDefect : amlc_claim_bar :=
  {| amlc_bar_presence_field := amlc_bar_present;
     amlc_bar_defect_total := 0 |}.

Definition amlc_claim_bar_zero_defect (b : amlc_claim_bar) : bool :=
  match amlc_bar_presence_field b with
  | amlc_bar_absent => false
  | amlc_bar_present => Nat.eqb (amlc_bar_defect_total b) 0
  end.

Lemma amlc_claim_bar_zero_defect_true :
  amlc_claim_bar_zero_defect assay_measurement_landauerClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma amlc_claim_bar_absent_not_zero_defect :
  amlc_claim_bar_zero_defect assay_measurement_landauerClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive amlc_conservation_verdict : Type :=
  | amlc_verdict_unwired_ok
  | amlc_verdict_named_ok
  | amlc_verdict_design_ok
  | amlc_verdict_trivial_refuse
  | amlc_verdict_xor_refuse
  | amlc_verdict_green_invent_refuse
  | amlc_verdict_proved_without_bar_refuse
  | amlc_verdict_production_wired_refuse
  | amlc_verdict_parallel_assay_measurement_landauer_axiom_refuse
  | amlc_verdict_species_id_smuggle_refuse
  | amlc_verdict_extra_element_id_refuse
  | amlc_verdict_extra_assay_measurement_landauer_force_refuse
  | amlc_verdict_cpu_heat_wall_clock_smuggle_refuse.

Definition amlc_conservation_verdict_ok (v : amlc_conservation_verdict) : bool :=
  match v with
  | amlc_verdict_unwired_ok => true
  | amlc_verdict_named_ok => true
  | amlc_verdict_design_ok => true
  | _ => false
  end.

Definition assayMeasurementLandauerBundleNontrivial (b : amlc_channel_bundle) : bool :=
  Nat.ltb 0 (assayMeasurementLandauerBundlePresentCount b).

Definition evaluate_assayMeasurementLandauer_bundle
  (m : AssayMeasurementLandauerConservationModality)
  (b : amlc_channel_bundle)
  (bar : amlc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : amlc_conservation_verdict :=
  if claim_physics_green
  then amlc_verdict_green_invent_refuse
  else if claim_proved
       then amlc_verdict_proved_without_bar_refuse
       else if negb (assayMeasurementLandauerBundleNontrivial b)
            then amlc_verdict_trivial_refuse
            else if amllXorClassifierIncompatible claim_xor_classifier b
                 then amlc_verdict_xor_refuse
                 else
                   match m with
                   | assay_measurement_landauer_conservation_unwired =>
                       if assayMeasurementLandauerBundleIsConcurrentProduct b
                       then amlc_verdict_named_ok
                       else amlc_verdict_design_ok
                   | assay_measurement_landauer_conservation_assumed
                   | assay_measurement_landauer_conservation_surrogate =>
                       amlc_verdict_design_ok
                   | assay_measurement_landauer_conservation_proved =>
                       amlc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_assayMeasurementLandauer_conservation_close
  (m : AssayMeasurementLandauerConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : amlc_conservation_verdict :=
  if claim_physics_green
  then amlc_verdict_green_invent_refuse
  else if claim_production_wired
  then amlc_verdict_production_wired_refuse
  else
    match m with
    | assay_measurement_landauer_conservation_unwired => amlc_verdict_unwired_ok
    | assay_measurement_landauer_conservation_assumed
    | assay_measurement_landauer_conservation_proved
    | assay_measurement_landauer_conservation_surrogate => amlc_verdict_named_ok
    end.

Definition assay_measurement_landauer_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_assayMeasurementLandauer_conservation_close
          assay_measurement_landauer_conservation_proved claim_physics_green claim_production_wired with
  | amlc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive amlc_conservation_law : Type :=
  | amlc_law_conserved
  | amlc_law_named_ok
  | amlc_law_trivial_refuse
  | amlc_law_green_invent_refuse.

Definition amlc_conservation_law_count : nat := 4.

Lemma amlc_conservation_law_count_is_four :
  amlc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive amlc_conservation_law_witness : Type :=
  | amlc_law_witness_open
  | amlc_law_witness_proved.

Definition evaluate_amlc_conservation_law_witness
  (law : amlc_conservation_law)
  (m : AssayMeasurementLandauerConservationModality)
  : amlc_conservation_law_witness :=
  match m with
  | assay_measurement_landauer_conservation_unwired
  | assay_measurement_landauer_conservation_assumed
  | assay_measurement_landauer_conservation_surrogate => amlc_law_witness_open
  | assay_measurement_landauer_conservation_proved => amlc_law_witness_proved
  end.

Lemma all_amlc_conservation_laws_open_at_unwired :
  evaluate_amlc_conservation_law_witness amlc_law_conserved
    assay_measurement_landauer_conservation_unwired = amlc_law_witness_open /\
  evaluate_amlc_conservation_law_witness amlc_law_named_ok
    assay_measurement_landauer_conservation_unwired = amlc_law_witness_open /\
  evaluate_amlc_conservation_law_witness amlc_law_trivial_refuse
    assay_measurement_landauer_conservation_unwired = amlc_law_witness_open /\
  evaluate_amlc_conservation_law_witness amlc_law_green_invent_refuse
    assay_measurement_landauer_conservation_unwired = amlc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-21 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition assayMeasurementLandauerConservationProved : bool := false.

Lemma assay_measurement_landauer_conservation_proved_false :
  assayMeasurementLandauerConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_unwired false false =
  amlc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_unwired false false =
  amlc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_unwired false false) =
  true.
Proof.
  unfold amlc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Au Z=79 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma au79_witness_named_ok :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false false =
  amlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_au79_assay_measurement_landauer_conservation :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false false =
  amlc_verdict_named_ok /\
  assayMeasurementLandauerBundleIsConcurrentProduct assayMeasurementLandauerAu79Witness = true /\
  gold_atomic_number_z = 79 /\
  pattern_class_assay_idx = 21.
Proof.
  repeat split; reflexivity.
Qed.

Lemma amlc_named_close_ok :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_proved false false =
  amlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_assay_measurement_landauer_conservation_close :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_proved false false =
  amlc_verdict_named_ok /\
  assay_measurement_landauer_conservation_authorized false false = true.
Proof.
  split.
  - apply amlc_named_close_ok.
  - unfold assay_measurement_landauer_conservation_authorized.
    rewrite amlc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — assay_measurement_landauer refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerEmptyWitness
    assay_measurement_landauerClaimBarAbsent false false false =
  amlc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerEmptyWitness
    assay_measurement_landauerClaimBarAbsent false false false =
  amlc_verdict_trivial_refuse /\
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_bundle
       assay_measurement_landauer_conservation_unwired
       assayMeasurementLandauerEmptyWitness
       assay_measurement_landauerClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold amlc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent true false false =
  amlc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent true false false =
  amlc_verdict_xor_refuse /\
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_bundle
       assay_measurement_landauer_conservation_unwired
       assayMeasurementLandauerAu79Witness
       assay_measurement_landauerClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold amlc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_unwired true false =
  amlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_unwired true false) =
  false.
Proof.
  unfold amlc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_amlc_bundle_refuse :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false true false =
  amlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — assay_measurement_landauer refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false true =
  amlc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false true =
  amlc_verdict_proved_without_bar_refuse /\
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_bundle
       assay_measurement_landauer_conservation_unwired
       assayMeasurementLandauerAu79Witness
       assay_measurement_landauerClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold amlc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — assay_measurement_landauer lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_proved false true =
  amlc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_proved false true) =
  false.
Proof.
  unfold amlc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel assay_measurement_landauer axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition assayMeasurementLandauerConservationAuthority : string :=
  "umst/umst-chem/src/assay_measurement_landauer.rs".

Definition parallelAssayMeasurementLandauerAxiomTag : string := "parallel_assay_measurement_landauer_axiom".

Lemma parallel_assay_measurement_landauer_axiom_refuse :
  assayMeasurementLandauerConservationAuthority <>
  parallelAssayMeasurementLandauerAxiomTag /\
  assayMeasurementLandauerConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply assay_measurement_landauer_conservation_proved_false.
Qed.

Theorem parallel_assay_measurement_landauer_axiom_not_minted :
  assayMeasurementLandauerConservationAuthority =
  "umst/umst-chem/src/assay_measurement_landauer.rs" /\
  assayMeasurementLandauerConservationProved = false /\
  assayMeasurementLandauerConservationAuthority <> parallelAssayMeasurementLandauerAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — G type-only ≠ L1 SpeciesId                 *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "cpu_heat_wall_clock_not_assay_not_named_object".

Definition assayMeasurementLandauerConservationFraming : string :=
  "second_law_conservation_assay_measurement_landauer_measurement_landauer_floor_one_axiom".

Lemma species_id_smuggle_refuse :
  assayMeasurementLandauerConservationFraming <>
  speciesIdSmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_assay_idx = 21.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem measurement_landauer_floor_not_species_id_smuggle :
  assayMeasurementLandauerConservationFraming <>
  speciesIdSmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_assay_idx = 21 /\
  assayMeasurementLandauerConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — assay_measurement_landauer ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "cpu_heat_wall_clock_smuggle_as_landauer_floor".

Lemma extra_element_id_refuse :
  assayMeasurementLandauerConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  assayMeasurementLandauerConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — assay_measurement_landauer ≠ extra assay_measurement_landauer force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraAssayMeasurementLandauerForceFraming : string :=
  "extra_assay_measurement_landauer_force_axiom_minted_as_26th_law".

Definition assay_measurement_landauerBarrierAuthority : string :=
  "umst/umst-chem/src/l0_tables/assay_measurement_landauer.rs".

Lemma extra_assay_measurement_landauer_force_refuse :
  assayMeasurementLandauerConservationFraming <>
  extraAssayMeasurementLandauerForceFraming /\
  assay_measurement_landauerBarrierAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem assay_measurement_landauer_not_extra_assay_measurement_landauer_force :
  assayMeasurementLandauerConservationFraming <>
  extraAssayMeasurementLandauerForceFraming /\
  assay_measurement_landauerBarrierAuthority =
  "umst/umst-chem/src/l0_tables/assay_measurement_landauer.rs" /\
  assayMeasurementLandauerConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  CPU-heat / wall-clock smuggle refuse — floor ≠ CPU heat smuggle    *)
(* ------------------------------------------------------------------ *)

Definition cpuHeatWallClockSmuggleFraming : string :=
  "wall_clock_cpu_heat_smuggle_not_measurement_landauer_floor".

Lemma cpu_heat_wall_clock_smuggle_refuse :
  assayMeasurementLandauerConservationFraming <>
  cpuHeatWallClockSmuggleFraming /\
  measurement_landauer_floor_channel_tag = "measurement_landauer_floor".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem measurement_landauer_not_cpu_heat_smuggle :
  assayMeasurementLandauerConservationFraming <>
  cpuHeatWallClockSmuggleFraming /\
  cpu_heat_wall_clock_not_assay_channel_tag = "cpu_heat_wall_clock_not_assay" /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  AssayMeasurementLandauer **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition amlc_conservation_coherence_scaffold : bool :=
  amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_proved false false) &&
  negb (amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_unwired true false)) &&
  negb (amlc_conservation_verdict_ok
    (evaluate_assayMeasurementLandauer_conservation_close
       assay_measurement_landauer_conservation_proved false true)).

Lemma amlc_conservation_coherence_scaffold_true :
  amlc_conservation_coherence_scaffold = true.
Proof.
  unfold amlc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem amlc_conservation_coherence_scaffold_theorem :
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_proved false false =
    amlc_verdict_named_ok /\
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_unwired true false =
    amlc_verdict_green_invent_refuse /\
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_proved false true =
    amlc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition amlc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition amlc_conservation_knowing_fiber_ok : bool :=
  amlc_conservation_fiber_ok fiber_quantum_knowing.

Definition amlc_conservation_meso_acting_ok : bool :=
  amlc_conservation_fiber_ok fiber_meso_acting.

Lemma amlc_conservation_knowing_fiber_ok_true :
  amlc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma amlc_conservation_meso_acting_not_ok :
  amlc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem amlc_conservation_routes_knowing_not_meso :
  amlc_conservation_knowing_fiber_ok = true /\
  amlc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply amlc_conservation_knowing_fiber_ok_true.
  - apply amlc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  amlc_conservation_knowing_fiber_ok &&
  negb amlc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, amlc_conservation_knowing_fiber_ok,
    amlc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-21 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem assay_measurement_landauer_conservation_fixture_scaffold :
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false false =
    amlc_verdict_named_ok /\
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerEmptyWitness
    assay_measurement_landauerClaimBarAbsent false false false =
    amlc_verdict_trivial_refuse /\
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent true false false =
    amlc_verdict_xor_refuse /\
  evaluate_assayMeasurementLandauer_bundle
    assay_measurement_landauer_conservation_unwired
    assayMeasurementLandauerAu79Witness
    assay_measurement_landauerClaimBarAbsent false false true =
    amlc_verdict_proved_without_bar_refuse /\
  evaluate_assayMeasurementLandauer_conservation_close
    assay_measurement_landauer_conservation_unwired false false =
    amlc_verdict_unwired_ok /\
  amlc_conservation_knowing_fiber_ok = true /\
  amlc_conservation_meso_acting_ok = false /\
  assayMeasurementLandauerConservationProved = false /\
  amllProductNotXor = true /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — assay_measurement_landauer) *)
(* ------------------------------------------------------------------ *)

Definition chemL0AssayMeasurementLandauerAuthority : string :=
  "umst/umst-chem/src/assay_measurement_landauer.rs".

Definition chemL0AssayMeasurementLandauerTableAuthority : string :=
  "umst/umst-chem/src/assay_measurement_landauer.rs".

Definition interactPartialityAuthority : string :=
  "umst/umst-chem/src/l0_tables/assay_measurement_landauer.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeAssayMeasurementLandauerCellId : string := "CHEM-L0-EDGE-ASSAY".

Definition assayMeasurementLandauerConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ASSAY-MEASUREMENT-LANDAUER-CONSERVATION".

Definition assayMeasurementLandauerConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ASSAY-MEASUREMENT-LANDAUER-CONSERVATION AssayMeasurementLandauerConservationModality Unwired Assumed Proved Surrogate four-step lattice assayMeasurementLandauerConservationProved false evaluateAssayMeasurementLandauerBundle evaluateAssayMeasurementLandauerConservation named class 21 assay_measurement_landauer Au Z=79 measurement pays Landauer floor cpu heat wall clock smuggle refuse not parallel assay axiom refuse species id smuggle refuse extra element id Z=119 refuse extra assay force refuse assay ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs".

Lemma assay_measurement_landauer_conservation_cell_id :
  assayMeasurementLandauerConservationCellId =
  "CHEM-FORMAL-Q-COQ-ASSAY-MEASUREMENT-LANDAUER-CONSERVATION".
Proof. reflexivity. Qed.

Lemma assay_measurement_landauer_conservation_cites_l0_table :
  chemL0AssayMeasurementLandauerTableAuthority <> "".
Proof. discriminate. Qed.

Lemma assay_measurement_landauer_conservation_authority_path :
  assayMeasurementLandauerConservationAuthority =
  "umst/umst-chem/src/assay_measurement_landauer.rs".
Proof. reflexivity. Qed.

Lemma assay_measurement_landauer_conservation_cites_l0_ore02 :
  chemL0AssayMeasurementLandauerAuthority <> "".
Proof. discriminate. Qed.

Lemma assay_measurement_landauer_conservation_cites_marker :
  amllConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma assay_measurement_landauer_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma assay_measurement_landauer_conservation_cites_ore02_cell :
  chemL0EdgeAssayMeasurementLandauerCellId = "CHEM-L0-EDGE-ASSAY".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma assay_measurement_landauer_not_26th_axiom :
  assayMeasurementLandauerConservationFraming <> parallelAssayMeasurementLandauerAxiomTag.
Proof. discriminate. Qed.

Lemma assay_measurement_landauer_second_law_conservation_framing :
  assayMeasurementLandauerConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Measurement Landauer floor — named object not CPU-heat smuggle      *)
(* ------------------------------------------------------------------ *)

Definition measurementLandauerFloorNamedObject : string :=
  "measurement_landauer_floor_on_assay_measurement_landauer_morphism".

Lemma measurement_landauer_floor_not_cpu_heat_smuggle :
  measurementLandauerFloorNamedObject <>
  cpuHeatWallClockSmuggleFraming /\
  cpu_heat_wall_clock_not_assay_channel_tag = "cpu_heat_wall_clock_not_assay".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem measurement_landauer_floor_is_named_object_not_cpu_heat :
  measurementLandauerFloorNamedObject <>
  cpuHeatWallClockSmuggleFraming /\
  measurement_landauer_floor_channel_tag = "measurement_landauer_floor" /\
  assayMeasurementLandauerConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Measurement Landauer floor refuse — not parallel assay axiom        *)
(* ------------------------------------------------------------------ *)

Definition measurementLandauerFloorFraming : string :=
  "measurement_landauer_floor_not_extra_force".

Lemma measurement_landauer_floor_not_extra_force_refuse :
  measurementLandauerFloorFraming <>
  extraAssayMeasurementLandauerForceFraming /\
  measurement_landauer_floor_channel_tag = "measurement_landauer_floor".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem assay_measurement_landauer_measurement_landauer_floor_not_extra_force :
  measurementLandauerFloorFraming <>
  extraAssayMeasurementLandauerForceFraming /\
  assay_measurement_landauerBarrierAuthority =
  "umst/umst-chem/src/l0_tables/assay_measurement_landauer.rs" /\
  assayMeasurementLandauerConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs not wired (freeze-safe until lift)                 *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.

Definition wave100EosRsWired : bool := false.

Lemma wave100_lib_rs_not_wired :
  wave100LibRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_eos_rs_not_wired :
  wave100EosRsWired = false.
Proof. reflexivity. Qed.

Definition wave100FreezeTag : string :=
  "WAVE100 freeze — not wired lib.rs".

Lemma wave100_freeze_tag_nonempty :
  wave100FreezeTag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma assay_measurement_landauer_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma assay_measurement_landauer_conservation_modality_unwired :
  assayMeasurementLandauerConservationModalityCurrent =
  assay_measurement_landauer_conservation_unwired.
Proof. reflexivity. Qed.

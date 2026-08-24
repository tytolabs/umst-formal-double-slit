(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: GdExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Gd Z=64 f-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Gd Z=64 4f7 5d1 6s2 named Madelung exception; Y Z=39 / Cm Z=96 homolog not Gd copy. *)
(*  gdExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **gd_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive GdExceptionContinuumModality : Type :=
  | gd_exception_continuum_unwired
  | gd_exception_continuum_assumed
  | gd_exception_continuum_proved
  | gd_exception_continuum_surrogate.

Definition gdExceptionContinuumModalityCurrent :
  GdExceptionContinuumModality :=
  gd_exception_continuum_unwired.

Definition gd_exception_continuum_lattice_cardinality : nat := 4.

Lemma gd_exception_continuum_lattice_cardinality_is_four :
  gd_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma gd_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb gd_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold gd_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — gd_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_gd_exception_continuum_idx : nat := 14.

Lemma pattern_class_gd_exception_continuum_idx_is_14 :
  pattern_class_gd_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma gd_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_gd_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_gd_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_gd_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_gd_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_gd_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_gd_exception_continuum_tag_nonempty :
  pattern_class_gd_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_gd_exception_continuum_tag_nonempty :
  north_star_class_14_gd_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Gd Z=64 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition gadolinium_atomic_number_z : nat := 64.

Lemma gadolinium_atomic_number_z_is_64 :
  gadolinium_atomic_number_z = 64.
Proof. reflexivity. Qed.

Definition gadolinium_z_valid : bool :=
  Nat.ltb 0 gadolinium_atomic_number_z &&
  Nat.leb gadolinium_atomic_number_z iupac_table_cardinality.

Lemma gadolinium_z_valid_true : gadolinium_z_valid = true.
Proof.
  unfold gadolinium_z_valid, gadolinium_atomic_number_z, iupac_table_cardinality.
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
(*  Gd Z=64 occupancy pins — 4f⁷5d¹6s² observed vs Madelung predicted  *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition gd_element_symbol : string := "Gd".

Definition gd_observed_occupancy_tag : string := "4f75d16s2".

Definition gd_predicted_occupancy_tag : string := "6s24f8".

Definition gd_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1".

Definition gd_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f8".

Definition y_homolog_observed_occupancy_tag : string := "4d15s2".

Definition yttrium_homolog_z : nat := 39.

Lemma yttrium_homolog_z_is_39 :
  yttrium_homolog_z = 39.
Proof. reflexivity. Qed.

Definition cm_homolog_observed_occupancy_tag : string := "5f76d17s2".

Definition curium_homolog_z : nat := 96.

Lemma curium_homolog_z_is_96 :
  curium_homolog_z = 96.
Proof. reflexivity. Qed.

Lemma gd_element_symbol_nonempty :
  gd_element_symbol <> "".
Proof. discriminate. Qed.

Lemma gd_observed_occupancy_tag_nonempty :
  gd_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma gd_predicted_occupancy_tag_nonempty :
  gd_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma gd_observed_ne_predicted_occupancy :
  gd_observed_occupancy_tag <> gd_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma gd_observed_ne_predicted_subshell :
  gd_observed_subshell_notation <> gd_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma gd_y_homolog_occupancy_not_copy :
  gd_observed_occupancy_tag <> y_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Lemma gd_cm_homolog_occupancy_not_copy :
  gd_observed_occupancy_tag <> cm_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "named_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "named_exception".
Proof. reflexivity. Qed.

Definition gd_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma gd_exception_continuum_factor_tag_nonempty :
  gd_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive gdec_channel_slot : Type :=
  | gdec_slot_unwired
  | gdec_slot_absent
  | gdec_slot_present.

Definition gdec_channel_slot_beq (s1 s2 : gdec_channel_slot) : bool :=
  match s1, s2 with
  | gdec_slot_unwired, gdec_slot_unwired => true
  | gdec_slot_absent, gdec_slot_absent => true
  | gdec_slot_present, gdec_slot_present => true
  | _, _ => false
  end.

Definition gdec_channel_slot_is_present (s : gdec_channel_slot) : bool :=
  match s with
  | gdec_slot_present => true
  | _ => false
  end.

Definition gdExceptionContinuumProductChannelCount : nat := 3.

Lemma gd_exception_continuum_product_channel_count_is_three :
  gdExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 gd_exception_continuum. *)
Definition gdec_channel_occupancy_engine_sort : nat := 0.
Definition gdec_channel_observed_override : nat := 1.
Definition gdec_channel_named_exception_continuum : nat := 2.

Lemma gdec_channel_occupancy_engine_sort_idx_is_0 :
  gdec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma gdec_channel_observed_override_idx_is_1 :
  gdec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma gdec_channel_class9_gd_exception_continuum_idx_is_2 :
  gdec_channel_named_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition gdec_channel_bundle : Type := nat -> gdec_channel_slot.

Definition gdExceptionContinuumBundleAllUnwired : gdec_channel_bundle :=
  fun _ => gdec_slot_unwired.

Definition gdExceptionContinuumBundleAt (b : gdec_channel_bundle) (idx : nat)
  (slot : gdec_channel_slot) : gdec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition gdExceptionContinuumBundleWithPresent
  (b : gdec_channel_bundle) (idx : nat) : gdec_channel_bundle :=
  gdExceptionContinuumBundleAt b idx gdec_slot_present.

Fixpoint count_gdec_present_up_to (b : gdec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if gdec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_gdec_present_up_to b i + add
  end.

Definition gdExceptionContinuumBundlePresentCount (b : gdec_channel_bundle) : nat :=
  count_gdec_present_up_to b gdExceptionContinuumProductChannelCount.

Definition gdExceptionContinuumBundleHolds (b : gdec_channel_bundle) (idx : nat) : bool :=
  gdec_channel_slot_is_present (b idx).

Definition gdExceptionContinuumBundleIsConcurrentProduct (b : gdec_channel_bundle) : bool :=
  Nat.leb 2 (gdExceptionContinuumBundlePresentCount b).

(* Gd Z=64 interact restriction + G-min + class 14 gd_exception_continuum concurrent witness. *)
Definition gdExceptionContinuumGd64Witness : gdec_channel_bundle :=
  gdExceptionContinuumBundleWithPresent
    (gdExceptionContinuumBundleWithPresent
      (gdExceptionContinuumBundleWithPresent gdExceptionContinuumBundleAllUnwired
        gdec_channel_occupancy_engine_sort)
      gdec_channel_observed_override)
    gdec_channel_named_exception_continuum.

Definition gdExceptionContinuumEmptyWitness : gdec_channel_bundle :=
  gdExceptionContinuumBundleAllUnwired.

Definition gdExceptionContinuumSinglePresent : gdec_channel_bundle :=
  gdExceptionContinuumBundleWithPresent gdExceptionContinuumBundleAllUnwired
    gdec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  gdExceptionContinuumBundleHolds gdExceptionContinuumGd64Witness
    gdec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  gdExceptionContinuumBundleHolds gdExceptionContinuumGd64Witness
    gdec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_gd_exception_continuum_channel_present :
  gdExceptionContinuumBundleHolds gdExceptionContinuumGd64Witness
    gdec_channel_named_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma gd64_witness_present_count_is_three :
  gdExceptionContinuumBundlePresentCount gdExceptionContinuumGd64Witness = 3.
Proof. reflexivity. Qed.

Lemma gd64_witness_is_concurrent_product :
  gdExceptionContinuumBundleIsConcurrentProduct gdExceptionContinuumGd64Witness = true.
Proof.
  unfold gdExceptionContinuumBundleIsConcurrentProduct.
  rewrite gd64_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  gdExceptionContinuumBundlePresentCount gdExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  gdExceptionContinuumBundleIsConcurrentProduct gdExceptionContinuumEmptyWitness = false.
Proof.
  unfold gdExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  gdExceptionContinuumBundlePresentCount gdExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  gdExceptionContinuumBundleIsConcurrentProduct gdExceptionContinuumSinglePresent = false.
Proof.
  unfold gdExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive gdec_xor_posture : Type :=
  | gdec_xor_exclusive
  | gdec_xor_concurrent_product.

Definition gdecXorClassifierMarker : string := "chem_l0_gd_exception_continuum_xor_classifier_v1".
Definition gdecConcurrentProductMarker : string := "chem_int_gd_exception_continuum_product_v1".

Lemma gdec_xor_marker_ne_concurrent_product_marker :
  gdecXorClassifierMarker <> gdecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition gdecXorClassifierIncompatible (claim_xor : bool)
  (b : gdec_channel_bundle) : bool :=
  claim_xor && gdExceptionContinuumBundleIsConcurrentProduct b.

Lemma gdec_xor_refuse_on_gd64_witness :
  gdecXorClassifierIncompatible true gdExceptionContinuumGd64Witness = true.
Proof.
  unfold gdecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma gdec_xor_ok_on_concurrent_product_claim :
  gdecXorClassifierIncompatible false gdExceptionContinuumGd64Witness = false.
Proof. reflexivity. Qed.

Definition gdecProductNotXor : bool :=
  gdExceptionContinuumBundleIsConcurrentProduct gdExceptionContinuumGd64Witness &&
  gdecXorClassifierIncompatible true gdExceptionContinuumGd64Witness.

Lemma gdec_product_not_xor_true : gdecProductNotXor = true.
Proof.
  unfold gdecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  gdecProductNotXor = true /\
  Nat.leb 2 (gdExceptionContinuumBundlePresentCount
    gdExceptionContinuumGd64Witness) = true /\
  gdecXorClassifierMarker <> gdecConcurrentProductMarker.
Proof.
  split.
  - apply gdec_product_not_xor_true.
  - split.
    + rewrite gd64_witness_present_count_is_three.
      reflexivity.
    + apply gdec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive gdec_bar_presence : Type :=
  | gdec_bar_absent
  | gdec_bar_present.

Record gdec_claim_bar : Type := {
  gdec_bar_presence_field : gdec_bar_presence;
  gdec_bar_defect_total : nat
}.

Definition gdExceptionContinuumClaimBarAbsent : gdec_claim_bar :=
  {| gdec_bar_presence_field := gdec_bar_absent;
     gdec_bar_defect_total := 0 |}.

Definition gdExceptionContinuumClaimBarZeroDefect : gdec_claim_bar :=
  {| gdec_bar_presence_field := gdec_bar_present;
     gdec_bar_defect_total := 0 |}.

Definition gdec_claim_bar_zero_defect (b : gdec_claim_bar) : bool :=
  match gdec_bar_presence_field b with
  | gdec_bar_absent => false
  | gdec_bar_present => Nat.eqb (gdec_bar_defect_total b) 0
  end.

Lemma gdec_claim_bar_zero_defect_true :
  gdec_claim_bar_zero_defect gdExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma gdec_claim_bar_absent_not_zero_defect :
  gdec_claim_bar_zero_defect gdExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive gdec_conservation_verdict : Type :=
  | gdec_verdict_unwired_ok
  | gdec_verdict_named_ok
  | gdec_verdict_design_ok
  | gdec_verdict_trivial_refuse
  | gdec_verdict_xor_refuse
  | gdec_verdict_green_invent_refuse
  | gdec_verdict_proved_without_bar_refuse
  | gdec_verdict_production_wired_refuse
  | gdec_verdict_parallel_gd_exception_continuum_axiom_refuse
  | gdec_verdict_species_id_smuggle_refuse
  | gdec_verdict_extra_element_id_refuse
  | gdec_verdict_extra_gd_exception_continuum_force_refuse
  | gdec_verdict_tp_float_pin_refuse.

Definition gdec_conservation_verdict_ok (v : gdec_conservation_verdict) : bool :=
  match v with
  | gdec_verdict_unwired_ok => true
  | gdec_verdict_named_ok => true
  | gdec_verdict_design_ok => true
  | _ => false
  end.

Definition gdExceptionContinuumBundleNontrivial (b : gdec_channel_bundle) : bool :=
  Nat.ltb 0 (gdExceptionContinuumBundlePresentCount b).

Definition evaluate_gd_exception_continuum_bundle
  (m : GdExceptionContinuumModality)
  (b : gdec_channel_bundle)
  (bar : gdec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : gdec_conservation_verdict :=
  if claim_physics_green
  then gdec_verdict_green_invent_refuse
  else if claim_proved
       then gdec_verdict_proved_without_bar_refuse
       else if negb (gdExceptionContinuumBundleNontrivial b)
            then gdec_verdict_trivial_refuse
            else if gdecXorClassifierIncompatible claim_xor_classifier b
                 then gdec_verdict_xor_refuse
                 else
                   match m with
                   | gd_exception_continuum_unwired =>
                       if gdExceptionContinuumBundleIsConcurrentProduct b
                       then gdec_verdict_named_ok
                       else gdec_verdict_design_ok
                   | gd_exception_continuum_assumed
                   | gd_exception_continuum_surrogate =>
                       gdec_verdict_design_ok
                   | gd_exception_continuum_proved =>
                       gdec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_gd_exception_continuum_close
  (m : GdExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : gdec_conservation_verdict :=
  if claim_physics_green
  then gdec_verdict_green_invent_refuse
  else if claim_production_wired
  then gdec_verdict_production_wired_refuse
  else
    match m with
    | gd_exception_continuum_unwired => gdec_verdict_unwired_ok
    | gd_exception_continuum_assumed
    | gd_exception_continuum_proved
    | gd_exception_continuum_surrogate => gdec_verdict_named_ok
    end.

Definition gd_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_gd_exception_continuum_close
          gd_exception_continuum_proved claim_physics_green claim_production_wired with
  | gdec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive gdec_conservation_law : Type :=
  | gdec_law_conserved
  | gdec_law_named_ok
  | gdec_law_trivial_refuse
  | gdec_law_green_invent_refuse.

Definition gdec_conservation_law_count : nat := 4.

Lemma gdec_conservation_law_count_is_four :
  gdec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive gdec_conservation_law_witness : Type :=
  | gdec_law_witness_open
  | gdec_law_witness_proved.

Definition evaluate_gdec_conservation_law_witness
  (law : gdec_conservation_law)
  (m : GdExceptionContinuumModality)
  : gdec_conservation_law_witness :=
  match m with
  | gd_exception_continuum_unwired
  | gd_exception_continuum_assumed
  | gd_exception_continuum_surrogate => gdec_law_witness_open
  | gd_exception_continuum_proved => gdec_law_witness_proved
  end.

Lemma all_gdec_conservation_laws_open_at_unwired :
  evaluate_gdec_conservation_law_witness gdec_law_conserved
    gd_exception_continuum_unwired = gdec_law_witness_open /\
  evaluate_gdec_conservation_law_witness gdec_law_named_ok
    gd_exception_continuum_unwired = gdec_law_witness_open /\
  evaluate_gdec_conservation_law_witness gdec_law_trivial_refuse
    gd_exception_continuum_unwired = gdec_law_witness_open /\
  evaluate_gdec_conservation_law_witness gdec_law_green_invent_refuse
    gd_exception_continuum_unwired = gdec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition gdExceptionContinuumProved : bool := false.

Lemma gd_exception_continuum_proved_false :
  gdExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_unwired false false =
  gdec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_unwired false false =
  gdec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_unwired false false) =
  true.
Proof.
  unfold gdec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Gd Z=64 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma gd64_witness_named_ok :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false false =
  gdec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_gd64_gd_exception_continuum :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false false =
  gdec_verdict_named_ok /\
  gdExceptionContinuumBundleIsConcurrentProduct gdExceptionContinuumGd64Witness = true /\
  gadolinium_atomic_number_z = 64 /\
  gd_observed_occupancy_tag = "4f75d16s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma gdec_named_close_ok :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_proved false false =
  gdec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_gd_exception_continuum_close :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_proved false false =
  gdec_verdict_named_ok /\
  gd_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply gdec_named_close_ok.
  - unfold gd_exception_continuum_authorized.
    rewrite gdec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — gd_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumEmptyWitness
    gdExceptionContinuumClaimBarAbsent false false false =
  gdec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumEmptyWitness
    gdExceptionContinuumClaimBarAbsent false false false =
  gdec_verdict_trivial_refuse /\
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_bundle
       gd_exception_continuum_unwired
       gdExceptionContinuumEmptyWitness
       gdExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold gdec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent true false false =
  gdec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent true false false =
  gdec_verdict_xor_refuse /\
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_bundle
       gd_exception_continuum_unwired
       gdExceptionContinuumGd64Witness
       gdExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold gdec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_unwired true false =
  gdec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_unwired true false) =
  false.
Proof.
  unfold gdec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_gdec_bundle_refuse :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false true false =
  gdec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — gd_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false true =
  gdec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false true =
  gdec_verdict_proved_without_bar_refuse /\
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_bundle
       gd_exception_continuum_unwired
       gdExceptionContinuumGd64Witness
       gdExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold gdec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — gd_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_proved false true =
  gdec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_proved false true) =
  false.
Proof.
  unfold gdec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel gd_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition gdExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelGdExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_gd_exception_continuum_axiom_refuse :
  gdExceptionContinuumAuthority <>
  parallelGdExceptionAxiomTag /\
  gdExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply gd_exception_continuum_proved_false.
Qed.

Theorem parallel_gd_exception_continuum_axiom_not_minted :
  gdExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  gdExceptionContinuumProved = false /\
  gdExceptionContinuumAuthority <> parallelGdExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "y_z39_occupancy_copied_onto_gd_z64".

Definition gdExceptionContinuumFraming : string :=
  "second_law_conservation_gd_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  gdExceptionContinuumFraming <>
  homologCopyFraming /\
  gadolinium_atomic_number_z = 64 /\
  gd_observed_occupancy_tag = "4f75d16s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem gd_y_homolog_not_occupancy_copy :
  gdExceptionContinuumFraming <>
  homologCopyFraming /\
  gadolinium_atomic_number_z = 64 /\
  yttrium_homolog_z = 39 /\
  gd_observed_occupancy_tag <> y_homolog_observed_occupancy_tag /\
  gdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — gd_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "gd_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  gdExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  gdExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  gadolinium_atomic_number_z = 64.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — gd_exception_continuum ≠ extra gd_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_gd_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/gd_exception_continuum_barrier.rs".

Lemma extra_gd_exception_continuum_force_refuse :
  gdExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem gd_exception_continuum_not_extra_gd_exception_continuum_force :
  gdExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/gd_exception_continuum_barrier.rs" /\
  gdExceptionContinuumProved = false.
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
  gdExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  gd_observed_occupancy_tag <> gd_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply gd_observed_ne_predicted_occupancy.
Qed.

Theorem gd_observed_override_not_madelung_family_smuggle :
  gdExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  gd_observed_occupancy_tag = "4f75d16s2" /\
  gd_predicted_occupancy_tag = "6s24f8" /\
  gdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply gd_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_gd_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  gdExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  gdExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  gadolinium_atomic_number_z = 64.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  GdExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition gdec_conservation_coherence_scaffold : bool :=
  gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_proved false false) &&
  negb (gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_unwired true false)) &&
  negb (gdec_conservation_verdict_ok
    (evaluate_gd_exception_continuum_close
       gd_exception_continuum_proved false true)).

Lemma gdec_conservation_coherence_scaffold_true :
  gdec_conservation_coherence_scaffold = true.
Proof.
  unfold gdec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem gdec_conservation_coherence_scaffold_theorem :
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_proved false false =
    gdec_verdict_named_ok /\
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_unwired true false =
    gdec_verdict_green_invent_refuse /\
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_proved false true =
    gdec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition gdec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition gdec_conservation_knowing_fiber_ok : bool :=
  gdec_conservation_fiber_ok fiber_quantum_knowing.

Definition gdec_conservation_meso_acting_ok : bool :=
  gdec_conservation_fiber_ok fiber_meso_acting.

Lemma gdec_conservation_knowing_fiber_ok_true :
  gdec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma gdec_conservation_meso_acting_not_ok :
  gdec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem gdec_conservation_routes_knowing_not_meso :
  gdec_conservation_knowing_fiber_ok = true /\
  gdec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply gdec_conservation_knowing_fiber_ok_true.
  - apply gdec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  gdec_conservation_knowing_fiber_ok &&
  negb gdec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, gdec_conservation_knowing_fiber_ok,
    gdec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem gd_exception_continuum_fixture_scaffold :
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false false =
    gdec_verdict_named_ok /\
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumEmptyWitness
    gdExceptionContinuumClaimBarAbsent false false false =
    gdec_verdict_trivial_refuse /\
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent true false false =
    gdec_verdict_xor_refuse /\
  evaluate_gd_exception_continuum_bundle
    gd_exception_continuum_unwired
    gdExceptionContinuumGd64Witness
    gdExceptionContinuumClaimBarAbsent false false true =
    gdec_verdict_proved_without_bar_refuse /\
  evaluate_gd_exception_continuum_close
    gd_exception_continuum_unwired false false =
    gdec_verdict_unwired_ok /\
  gdec_conservation_knowing_fiber_ok = true /\
  gdec_conservation_meso_acting_ok = false /\
  gdExceptionContinuumProved = false /\
  gdecProductNotXor = true /\
  gadolinium_atomic_number_z = 64.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Y Z=39 / Cm Z=96 homolog not Gd copy — period homolog ≠ identity    *)
(* ------------------------------------------------------------------ *)

Definition yttrium_atomic_number_z : nat := 39.

Lemma yttrium_atomic_number_z_is_39 :
  yttrium_atomic_number_z = 39.
Proof. reflexivity. Qed.

Definition yttrium_occupancy_tag : string := "4d15s2".

Definition curium_atomic_number_z : nat := 96.

Lemma curium_atomic_number_z_is_96 :
  curium_atomic_number_z = 96.
Proof. reflexivity. Qed.

Definition curium_occupancy_tag : string := "5f76d17s2".

Lemma y_cm_occupancy_tags_distinct :
  yttrium_occupancy_tag <> curium_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma y_cm_homolog_not_copy :
  gadolinium_atomic_number_z = 64 /\
  yttrium_atomic_number_z = 39 /\
  curium_atomic_number_z = 96 /\
  yttrium_occupancy_tag <> curium_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem y_cm_period_homolog_not_gd_occupancy_copy :
  gadolinium_atomic_number_z = 64 /\
  yttrium_atomic_number_z = 39 /\
  curium_atomic_number_z = 96 /\
  yttrium_occupancy_tag = "4d15s2" /\
  curium_occupancy_tag = "5f76d17s2" /\
  gd_observed_occupancy_tag <> yttrium_occupancy_tag /\
  gd_observed_occupancy_tag <> curium_occupancy_tag /\
  gdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — gd_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition gdExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition namedOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/NamedOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition gdExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-GD-EXCEPTION-CONTINUUM".

Definition gdExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-GD-EXCEPTION-CONTINUUM GdExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice gdExceptionContinuumProved false evaluateGdExceptionContinuumBundle evaluateGdExceptionContinuumClose named Gd Z=64 f-block occupancy exception continuum X29 occupancy engine sort observed override named_exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel gd exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Y Z=39 Cm Z=96 homolog not Gd 4f7 5d1 6s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 not lib.rs".

Lemma gd_exception_continuum_cell_id :
  gdExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-GD-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma gd_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma gd_exception_continuum_authority_path :
  gdExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma gd_exception_continuum_cites_l0_ore02 :
  gdExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma gd_exception_continuum_cites_marker :
  gdecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma gd_exception_continuum_cites_pattern_product :
  namedOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma gd_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma gd_exception_continuum_not_26th_axiom :
  gdExceptionContinuumFraming <> parallelGdExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma gd_exception_continuum_second_law_conservation_framing :
  gdExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_gd_exception_continuum_morphism".

Lemma tst_prior_art_not_named_object :
  dblockExceptionNamedObject <>
  madelungWalkFraming /\
  observed_override_channel_tag = "observed_override".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem named_exception_is_named_object_not_madelung_walk :
  dblockExceptionNamedObject <>
  madelungWalkFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort" /\
  gdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not gd_exception_continuum axiom / extra force     *)
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

Theorem gd_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/gd_exception_continuum_barrier.rs" /\
  gdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma gd_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma gd_exception_continuum_modality_unwired :
  gdExceptionContinuumModalityCurrent =
  gd_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition gdExceptionContinuumProductionWired : Prop := False.

Lemma gd_exception_continuum_not_production_wired :
  ~ gdExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


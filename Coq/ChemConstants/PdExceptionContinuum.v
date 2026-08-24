(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PdExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Pd Z=46 d-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Pd Z=46 4d10 5s0 d-block Madelung exception; Ni Z=28 / Pt Z=78 homolog not Pd copy. *)
(*  pdExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **pd_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PdExceptionContinuumModality : Type :=
  | pd_exception_continuum_unwired
  | pd_exception_continuum_assumed
  | pd_exception_continuum_proved
  | pd_exception_continuum_surrogate.

Definition pdExceptionContinuumModalityCurrent :
  PdExceptionContinuumModality :=
  pd_exception_continuum_unwired.

Definition pd_exception_continuum_lattice_cardinality : nat := 4.

Lemma pd_exception_continuum_lattice_cardinality_is_four :
  pd_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma pd_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb pd_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold pd_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — pd_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_pd_exception_continuum_idx : nat := 14.

Lemma pattern_class_pd_exception_continuum_idx_is_14 :
  pattern_class_pd_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma pd_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_pd_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_pd_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_pd_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_pd_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_pd_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_pd_exception_continuum_tag_nonempty :
  pattern_class_pd_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_pd_exception_continuum_tag_nonempty :
  north_star_class_14_pd_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Pd Z=46 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition palladium_atomic_number_z : nat := 46.

Lemma palladium_atomic_number_z_is_46 :
  palladium_atomic_number_z = 46.
Proof. reflexivity. Qed.

Definition palladium_z_valid : bool :=
  Nat.ltb 0 palladium_atomic_number_z &&
  Nat.leb palladium_atomic_number_z iupac_table_cardinality.

Lemma palladium_z_valid_true : palladium_z_valid = true.
Proof.
  unfold palladium_z_valid, palladium_atomic_number_z, iupac_table_cardinality.
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
(*  Pd Z=46 occupancy pins — 4d¹⁰5s⁰ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition pd_element_symbol : string := "Pd".

Definition pd_observed_occupancy_tag : string := "4d105s0".

Definition pd_predicted_occupancy_tag : string := "5s24d8".

Definition pd_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p64d10".

Definition pd_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d8".

Definition ni_homolog_observed_occupancy_tag : string := "3d84s2".

Definition nickel_homolog_z : nat := 28.

Lemma nickel_homolog_z_is_28 :
  nickel_homolog_z = 28.
Proof. reflexivity. Qed.

Lemma pd_element_symbol_nonempty :
  pd_element_symbol <> "".
Proof. discriminate. Qed.

Lemma pd_observed_occupancy_tag_nonempty :
  pd_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pd_predicted_occupancy_tag_nonempty :
  pd_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pd_observed_ne_predicted_occupancy :
  pd_observed_occupancy_tag <> pd_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma pd_observed_ne_predicted_subshell :
  pd_observed_subshell_notation <> pd_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma pd_homolog_occupancy_not_copy :
  pd_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "dblock_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Definition pd_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma pd_exception_continuum_factor_tag_nonempty :
  pd_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive pdec_channel_slot : Type :=
  | pdec_slot_unwired
  | pdec_slot_absent
  | pdec_slot_present.

Definition pdec_channel_slot_beq (s1 s2 : pdec_channel_slot) : bool :=
  match s1, s2 with
  | pdec_slot_unwired, pdec_slot_unwired => true
  | pdec_slot_absent, pdec_slot_absent => true
  | pdec_slot_present, pdec_slot_present => true
  | _, _ => false
  end.

Definition pdec_channel_slot_is_present (s : pdec_channel_slot) : bool :=
  match s with
  | pdec_slot_present => true
  | _ => false
  end.

Definition pdExceptionContinuumProductChannelCount : nat := 3.

Lemma pd_exception_continuum_product_channel_count_is_three :
  pdExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 pd_exception_continuum. *)
Definition pdec_channel_occupancy_engine_sort : nat := 0.
Definition pdec_channel_observed_override : nat := 1.
Definition pdec_channel_dblock_exception_continuum : nat := 2.

Lemma pdec_channel_occupancy_engine_sort_idx_is_0 :
  pdec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma pdec_channel_observed_override_idx_is_1 :
  pdec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma pdec_channel_class9_pd_exception_continuum_idx_is_2 :
  pdec_channel_dblock_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition pdec_channel_bundle : Type := nat -> pdec_channel_slot.

Definition pdExceptionContinuumBundleAllUnwired : pdec_channel_bundle :=
  fun _ => pdec_slot_unwired.

Definition pdExceptionContinuumBundleAt (b : pdec_channel_bundle) (idx : nat)
  (slot : pdec_channel_slot) : pdec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition pdExceptionContinuumBundleWithPresent
  (b : pdec_channel_bundle) (idx : nat) : pdec_channel_bundle :=
  pdExceptionContinuumBundleAt b idx pdec_slot_present.

Fixpoint count_pdec_present_up_to (b : pdec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if pdec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_pdec_present_up_to b i + add
  end.

Definition pdExceptionContinuumBundlePresentCount (b : pdec_channel_bundle) : nat :=
  count_pdec_present_up_to b pdExceptionContinuumProductChannelCount.

Definition pdExceptionContinuumBundleHolds (b : pdec_channel_bundle) (idx : nat) : bool :=
  pdec_channel_slot_is_present (b idx).

Definition pdExceptionContinuumBundleIsConcurrentProduct (b : pdec_channel_bundle) : bool :=
  Nat.leb 2 (pdExceptionContinuumBundlePresentCount b).

(* Pd Z=46 interact restriction + G-min + class 14 pd_exception_continuum concurrent witness. *)
Definition pdExceptionContinuumPd46Witness : pdec_channel_bundle :=
  pdExceptionContinuumBundleWithPresent
    (pdExceptionContinuumBundleWithPresent
      (pdExceptionContinuumBundleWithPresent pdExceptionContinuumBundleAllUnwired
        pdec_channel_occupancy_engine_sort)
      pdec_channel_observed_override)
    pdec_channel_dblock_exception_continuum.

Definition pdExceptionContinuumEmptyWitness : pdec_channel_bundle :=
  pdExceptionContinuumBundleAllUnwired.

Definition pdExceptionContinuumSinglePresent : pdec_channel_bundle :=
  pdExceptionContinuumBundleWithPresent pdExceptionContinuumBundleAllUnwired
    pdec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  pdExceptionContinuumBundleHolds pdExceptionContinuumPd46Witness
    pdec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  pdExceptionContinuumBundleHolds pdExceptionContinuumPd46Witness
    pdec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_pd_exception_continuum_channel_present :
  pdExceptionContinuumBundleHolds pdExceptionContinuumPd46Witness
    pdec_channel_dblock_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma pd46_witness_present_count_is_three :
  pdExceptionContinuumBundlePresentCount pdExceptionContinuumPd46Witness = 3.
Proof. reflexivity. Qed.

Lemma pd46_witness_is_concurrent_product :
  pdExceptionContinuumBundleIsConcurrentProduct pdExceptionContinuumPd46Witness = true.
Proof.
  unfold pdExceptionContinuumBundleIsConcurrentProduct.
  rewrite pd46_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  pdExceptionContinuumBundlePresentCount pdExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  pdExceptionContinuumBundleIsConcurrentProduct pdExceptionContinuumEmptyWitness = false.
Proof.
  unfold pdExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  pdExceptionContinuumBundlePresentCount pdExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  pdExceptionContinuumBundleIsConcurrentProduct pdExceptionContinuumSinglePresent = false.
Proof.
  unfold pdExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive pdec_xor_posture : Type :=
  | pdec_xor_exclusive
  | pdec_xor_concurrent_product.

Definition pdecXorClassifierMarker : string := "chem_l0_pd_exception_continuum_xor_classifier_v1".
Definition pdecConcurrentProductMarker : string := "chem_int_pd_exception_continuum_product_v1".

Lemma pdec_xor_marker_ne_concurrent_product_marker :
  pdecXorClassifierMarker <> pdecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition pdecXorClassifierIncompatible (claim_xor : bool)
  (b : pdec_channel_bundle) : bool :=
  claim_xor && pdExceptionContinuumBundleIsConcurrentProduct b.

Lemma pdec_xor_refuse_on_pd46_witness :
  pdecXorClassifierIncompatible true pdExceptionContinuumPd46Witness = true.
Proof.
  unfold pdecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma pdec_xor_ok_on_concurrent_product_claim :
  pdecXorClassifierIncompatible false pdExceptionContinuumPd46Witness = false.
Proof. reflexivity. Qed.

Definition pdecProductNotXor : bool :=
  pdExceptionContinuumBundleIsConcurrentProduct pdExceptionContinuumPd46Witness &&
  pdecXorClassifierIncompatible true pdExceptionContinuumPd46Witness.

Lemma pdec_product_not_xor_true : pdecProductNotXor = true.
Proof.
  unfold pdecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  pdecProductNotXor = true /\
  Nat.leb 2 (pdExceptionContinuumBundlePresentCount
    pdExceptionContinuumPd46Witness) = true /\
  pdecXorClassifierMarker <> pdecConcurrentProductMarker.
Proof.
  split.
  - apply pdec_product_not_xor_true.
  - split.
    + rewrite pd46_witness_present_count_is_three.
      reflexivity.
    + apply pdec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive pdec_bar_presence : Type :=
  | pdec_bar_absent
  | pdec_bar_present.

Record pdec_claim_bar : Type := {
  pdec_bar_presence_field : pdec_bar_presence;
  pdec_bar_defect_total : nat
}.

Definition pdExceptionContinuumClaimBarAbsent : pdec_claim_bar :=
  {| pdec_bar_presence_field := pdec_bar_absent;
     pdec_bar_defect_total := 0 |}.

Definition pdExceptionContinuumClaimBarZeroDefect : pdec_claim_bar :=
  {| pdec_bar_presence_field := pdec_bar_present;
     pdec_bar_defect_total := 0 |}.

Definition pdec_claim_bar_zero_defect (b : pdec_claim_bar) : bool :=
  match pdec_bar_presence_field b with
  | pdec_bar_absent => false
  | pdec_bar_present => Nat.eqb (pdec_bar_defect_total b) 0
  end.

Lemma pdec_claim_bar_zero_defect_true :
  pdec_claim_bar_zero_defect pdExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma pdec_claim_bar_absent_not_zero_defect :
  pdec_claim_bar_zero_defect pdExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive pdec_conservation_verdict : Type :=
  | pdec_verdict_unwired_ok
  | pdec_verdict_named_ok
  | pdec_verdict_design_ok
  | pdec_verdict_trivial_refuse
  | pdec_verdict_xor_refuse
  | pdec_verdict_green_invent_refuse
  | pdec_verdict_proved_without_bar_refuse
  | pdec_verdict_production_wired_refuse
  | pdec_verdict_parallel_pd_exception_continuum_axiom_refuse
  | pdec_verdict_species_id_smuggle_refuse
  | pdec_verdict_extra_element_id_refuse
  | pdec_verdict_extra_pd_exception_continuum_force_refuse
  | pdec_verdict_tp_float_pin_refuse.

Definition pdec_conservation_verdict_ok (v : pdec_conservation_verdict) : bool :=
  match v with
  | pdec_verdict_unwired_ok => true
  | pdec_verdict_named_ok => true
  | pdec_verdict_design_ok => true
  | _ => false
  end.

Definition pdExceptionContinuumBundleNontrivial (b : pdec_channel_bundle) : bool :=
  Nat.ltb 0 (pdExceptionContinuumBundlePresentCount b).

Definition evaluate_pd_exception_continuum_bundle
  (m : PdExceptionContinuumModality)
  (b : pdec_channel_bundle)
  (bar : pdec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : pdec_conservation_verdict :=
  if claim_physics_green
  then pdec_verdict_green_invent_refuse
  else if claim_proved
       then pdec_verdict_proved_without_bar_refuse
       else if negb (pdExceptionContinuumBundleNontrivial b)
            then pdec_verdict_trivial_refuse
            else if pdecXorClassifierIncompatible claim_xor_classifier b
                 then pdec_verdict_xor_refuse
                 else
                   match m with
                   | pd_exception_continuum_unwired =>
                       if pdExceptionContinuumBundleIsConcurrentProduct b
                       then pdec_verdict_named_ok
                       else pdec_verdict_design_ok
                   | pd_exception_continuum_assumed
                   | pd_exception_continuum_surrogate =>
                       pdec_verdict_design_ok
                   | pd_exception_continuum_proved =>
                       pdec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_pd_exception_continuum_close
  (m : PdExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : pdec_conservation_verdict :=
  if claim_physics_green
  then pdec_verdict_green_invent_refuse
  else if claim_production_wired
  then pdec_verdict_production_wired_refuse
  else
    match m with
    | pd_exception_continuum_unwired => pdec_verdict_unwired_ok
    | pd_exception_continuum_assumed
    | pd_exception_continuum_proved
    | pd_exception_continuum_surrogate => pdec_verdict_named_ok
    end.

Definition pd_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_pd_exception_continuum_close
          pd_exception_continuum_proved claim_physics_green claim_production_wired with
  | pdec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive pdec_conservation_law : Type :=
  | pdec_law_conserved
  | pdec_law_named_ok
  | pdec_law_trivial_refuse
  | pdec_law_green_invent_refuse.

Definition pdec_conservation_law_count : nat := 4.

Lemma pdec_conservation_law_count_is_four :
  pdec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive pdec_conservation_law_witness : Type :=
  | pdec_law_witness_open
  | pdec_law_witness_proved.

Definition evaluate_pdec_conservation_law_witness
  (law : pdec_conservation_law)
  (m : PdExceptionContinuumModality)
  : pdec_conservation_law_witness :=
  match m with
  | pd_exception_continuum_unwired
  | pd_exception_continuum_assumed
  | pd_exception_continuum_surrogate => pdec_law_witness_open
  | pd_exception_continuum_proved => pdec_law_witness_proved
  end.

Lemma all_pdec_conservation_laws_open_at_unwired :
  evaluate_pdec_conservation_law_witness pdec_law_conserved
    pd_exception_continuum_unwired = pdec_law_witness_open /\
  evaluate_pdec_conservation_law_witness pdec_law_named_ok
    pd_exception_continuum_unwired = pdec_law_witness_open /\
  evaluate_pdec_conservation_law_witness pdec_law_trivial_refuse
    pd_exception_continuum_unwired = pdec_law_witness_open /\
  evaluate_pdec_conservation_law_witness pdec_law_green_invent_refuse
    pd_exception_continuum_unwired = pdec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition pdExceptionContinuumProved : bool := false.

Lemma pd_exception_continuum_proved_false :
  pdExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_unwired false false =
  pdec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_unwired false false =
  pdec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_unwired false false) =
  true.
Proof.
  unfold pdec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pd Z=46 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pd46_witness_named_ok :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false false =
  pdec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pd46_pd_exception_continuum :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false false =
  pdec_verdict_named_ok /\
  pdExceptionContinuumBundleIsConcurrentProduct pdExceptionContinuumPd46Witness = true /\
  palladium_atomic_number_z = 46 /\
  pd_observed_occupancy_tag = "4d105s0".
Proof.
  repeat split; reflexivity.
Qed.

Lemma pdec_named_close_ok :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_proved false false =
  pdec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pd_exception_continuum_close :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_proved false false =
  pdec_verdict_named_ok /\
  pd_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply pdec_named_close_ok.
  - unfold pd_exception_continuum_authorized.
    rewrite pdec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — pd_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumEmptyWitness
    pdExceptionContinuumClaimBarAbsent false false false =
  pdec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumEmptyWitness
    pdExceptionContinuumClaimBarAbsent false false false =
  pdec_verdict_trivial_refuse /\
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_bundle
       pd_exception_continuum_unwired
       pdExceptionContinuumEmptyWitness
       pdExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold pdec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent true false false =
  pdec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent true false false =
  pdec_verdict_xor_refuse /\
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_bundle
       pd_exception_continuum_unwired
       pdExceptionContinuumPd46Witness
       pdExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold pdec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_unwired true false =
  pdec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_unwired true false) =
  false.
Proof.
  unfold pdec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_pdec_bundle_refuse :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false true false =
  pdec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — pd_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false true =
  pdec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false true =
  pdec_verdict_proved_without_bar_refuse /\
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_bundle
       pd_exception_continuum_unwired
       pdExceptionContinuumPd46Witness
       pdExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold pdec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — pd_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_proved false true =
  pdec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_proved false true) =
  false.
Proof.
  unfold pdec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel pd_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition pdExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelPdExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_pd_exception_continuum_axiom_refuse :
  pdExceptionContinuumAuthority <>
  parallelPdExceptionAxiomTag /\
  pdExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply pd_exception_continuum_proved_false.
Qed.

Theorem parallel_pd_exception_continuum_axiom_not_minted :
  pdExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  pdExceptionContinuumProved = false /\
  pdExceptionContinuumAuthority <> parallelPdExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "ni_z28_occupancy_copied_onto_pd_z46".

Definition pdExceptionContinuumFraming : string :=
  "second_law_conservation_pd_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  pdExceptionContinuumFraming <>
  homologCopyFraming /\
  palladium_atomic_number_z = 46 /\
  pd_observed_occupancy_tag = "4d105s0".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pd_ni_homolog_not_occupancy_copy :
  pdExceptionContinuumFraming <>
  homologCopyFraming /\
  palladium_atomic_number_z = 46 /\
  nickel_homolog_z = 28 /\
  pd_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag /\
  pdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — pd_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "pd_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  pdExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  pdExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  palladium_atomic_number_z = 46.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — pd_exception_continuum ≠ extra pd_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_pd_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/pd_exception_continuum_barrier.rs".

Lemma extra_pd_exception_continuum_force_refuse :
  pdExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem pd_exception_continuum_not_extra_pd_exception_continuum_force :
  pdExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pd_exception_continuum_barrier.rs" /\
  pdExceptionContinuumProved = false.
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
  pdExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pd_observed_occupancy_tag <> pd_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply pd_observed_ne_predicted_occupancy.
Qed.

Theorem pd_observed_override_not_madelung_family_smuggle :
  pdExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pd_observed_occupancy_tag = "4d105s0" /\
  pd_predicted_occupancy_tag = "5s24d8" /\
  pdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply pd_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_pd_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  pdExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  pdExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  palladium_atomic_number_z = 46.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  PdExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition pdec_conservation_coherence_scaffold : bool :=
  pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_proved false false) &&
  negb (pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_unwired true false)) &&
  negb (pdec_conservation_verdict_ok
    (evaluate_pd_exception_continuum_close
       pd_exception_continuum_proved false true)).

Lemma pdec_conservation_coherence_scaffold_true :
  pdec_conservation_coherence_scaffold = true.
Proof.
  unfold pdec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem pdec_conservation_coherence_scaffold_theorem :
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_proved false false =
    pdec_verdict_named_ok /\
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_unwired true false =
    pdec_verdict_green_invent_refuse /\
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_proved false true =
    pdec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition pdec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition pdec_conservation_knowing_fiber_ok : bool :=
  pdec_conservation_fiber_ok fiber_quantum_knowing.

Definition pdec_conservation_meso_acting_ok : bool :=
  pdec_conservation_fiber_ok fiber_meso_acting.

Lemma pdec_conservation_knowing_fiber_ok_true :
  pdec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma pdec_conservation_meso_acting_not_ok :
  pdec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem pdec_conservation_routes_knowing_not_meso :
  pdec_conservation_knowing_fiber_ok = true /\
  pdec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply pdec_conservation_knowing_fiber_ok_true.
  - apply pdec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  pdec_conservation_knowing_fiber_ok &&
  negb pdec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, pdec_conservation_knowing_fiber_ok,
    pdec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem pd_exception_continuum_fixture_scaffold :
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false false =
    pdec_verdict_named_ok /\
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumEmptyWitness
    pdExceptionContinuumClaimBarAbsent false false false =
    pdec_verdict_trivial_refuse /\
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent true false false =
    pdec_verdict_xor_refuse /\
  evaluate_pd_exception_continuum_bundle
    pd_exception_continuum_unwired
    pdExceptionContinuumPd46Witness
    pdExceptionContinuumClaimBarAbsent false false true =
    pdec_verdict_proved_without_bar_refuse /\
  evaluate_pd_exception_continuum_close
    pd_exception_continuum_unwired false false =
    pdec_verdict_unwired_ok /\
  pdec_conservation_knowing_fiber_ok = true /\
  pdec_conservation_meso_acting_ok = false /\
  pdExceptionContinuumProved = false /\
  pdecProductNotXor = true /\
  palladium_atomic_number_z = 46.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pt Z=78 homolog not Ni copy — period-6 d-block homolog ≠ identity  *)
(* ------------------------------------------------------------------ *)

Definition platinum_atomic_number_z : nat := 78.

Lemma platinum_atomic_number_z_is_78 :
  platinum_atomic_number_z = 78.
Proof. reflexivity. Qed.

Definition nickel_occupancy_tag : string := "3d84s2".

Definition platinum_occupancy_tag : string := "5d96s1".

Lemma nickel_platinum_occupancy_tags_distinct :
  nickel_occupancy_tag <> platinum_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma pt_ni_homolog_not_copy :
  palladium_atomic_number_z = 46 /\
  platinum_atomic_number_z = 78 /\
  nickel_occupancy_tag <> platinum_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pt_period6_homolog_not_ni_occupancy_copy :
  palladium_atomic_number_z = 46 /\
  platinum_atomic_number_z = 78 /\
  nickel_occupancy_tag = "3d84s2" /\
  platinum_occupancy_tag = "5d96s1" /\
  nickel_occupancy_tag <> platinum_occupancy_tag /\
  pdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pd_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition pdExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition pdExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-PD-EXCEPTION-CONTINUUM".

Definition pdExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PD-EXCEPTION-CONTINUUM PdExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice pdExceptionContinuumProved false evaluatePdExceptionContinuumBundle evaluatePdExceptionContinuum named Pd Z=46 d-block occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel ni exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Pt Z=78 homolog not Ni 3d8 4s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma pd_exception_continuum_cell_id :
  pdExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-PD-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma pd_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma pd_exception_continuum_authority_path :
  pdExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma pd_exception_continuum_cites_l0_ore02 :
  pdExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma pd_exception_continuum_cites_marker :
  pdecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma pd_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma pd_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma pd_exception_continuum_not_26th_axiom :
  pdExceptionContinuumFraming <> parallelPdExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma pd_exception_continuum_second_law_conservation_framing :
  pdExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_pd_exception_continuum_morphism".

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
  pdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not pd_exception_continuum axiom / extra force     *)
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

Theorem pd_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pd_exception_continuum_barrier.rs" /\
  pdExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma pd_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma pd_exception_continuum_modality_unwired :
  pdExceptionContinuumModalityCurrent =
  pd_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition pdExceptionContinuumProductionWired : Prop := False.

Lemma pd_exception_continuum_not_production_wired :
  ~ pdExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


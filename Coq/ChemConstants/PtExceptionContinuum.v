(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PtExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Pt Z=78 d-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Pt Z=78 5d9 6s1 NamedException; Ni Z=28 / Pd Z=46 homolog not Pt copy. *)
(*  ptExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **pt_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PtExceptionContinuumModality : Type :=
  | pt_exception_continuum_unwired
  | pt_exception_continuum_assumed
  | pt_exception_continuum_proved
  | pt_exception_continuum_surrogate.

Definition ptExceptionContinuumModalityCurrent :
  PtExceptionContinuumModality :=
  pt_exception_continuum_unwired.

Definition pt_exception_continuum_lattice_cardinality : nat := 4.

Lemma pt_exception_continuum_lattice_cardinality_is_four :
  pt_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma pt_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb pt_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold pt_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — pt_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_pt_exception_continuum_idx : nat := 14.

Lemma pattern_class_pt_exception_continuum_idx_is_14 :
  pattern_class_pt_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma pt_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_pt_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_pt_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_pt_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_pt_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_pt_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_pt_exception_continuum_tag_nonempty :
  pattern_class_pt_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_pt_exception_continuum_tag_nonempty :
  north_star_class_14_pt_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Pt Z=78 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition platinum_atomic_number_z : nat := 78.

Lemma platinum_atomic_number_z_is_78 :
  platinum_atomic_number_z = 78.
Proof. reflexivity. Qed.

Definition platinum_z_valid : bool :=
  Nat.ltb 0 platinum_atomic_number_z &&
  Nat.leb platinum_atomic_number_z iupac_table_cardinality.

Lemma platinum_z_valid_true : platinum_z_valid = true.
Proof.
  unfold platinum_z_valid, platinum_atomic_number_z, iupac_table_cardinality.
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
(*  Pt Z=78 occupancy pins — 5d⁹6s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition pt_element_symbol : string := "Pt".

Definition pt_observed_occupancy_tag : string := "5d96s1".

Definition pt_predicted_occupancy_tag : string := "5d8".

Definition pt_observed_subshell_notation : string :=
  "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1".

Definition pt_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8".

Definition ni_homolog_observed_occupancy_tag : string := "3d84s2".

Definition nickel_homolog_z : nat := 28.

Lemma nickel_homolog_z_is_28 :
  nickel_homolog_z = 28.
Proof. reflexivity. Qed.

Lemma pt_element_symbol_nonempty :
  pt_element_symbol <> "".
Proof. discriminate. Qed.

Lemma pt_observed_occupancy_tag_nonempty :
  pt_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pt_predicted_occupancy_tag_nonempty :
  pt_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pt_observed_ne_predicted_occupancy :
  pt_observed_occupancy_tag <> pt_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma pt_observed_ne_predicted_subshell :
  pt_observed_subshell_notation <> pt_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma pt_homolog_occupancy_not_copy :
  pt_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "dblock_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Definition pt_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma pt_exception_continuum_factor_tag_nonempty :
  pt_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive ptec_channel_slot : Type :=
  | ptec_slot_unwired
  | ptec_slot_absent
  | ptec_slot_present.

Definition ptec_channel_slot_beq (s1 s2 : ptec_channel_slot) : bool :=
  match s1, s2 with
  | ptec_slot_unwired, ptec_slot_unwired => true
  | ptec_slot_absent, ptec_slot_absent => true
  | ptec_slot_present, ptec_slot_present => true
  | _, _ => false
  end.

Definition ptec_channel_slot_is_present (s : ptec_channel_slot) : bool :=
  match s with
  | ptec_slot_present => true
  | _ => false
  end.

Definition ptExceptionContinuumProductChannelCount : nat := 3.

Lemma pt_exception_continuum_product_channel_count_is_three :
  ptExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 pt_exception_continuum. *)
Definition ptec_channel_occupancy_engine_sort : nat := 0.
Definition ptec_channel_observed_override : nat := 1.
Definition ptec_channel_dblock_exception_continuum : nat := 2.

Lemma ptec_channel_occupancy_engine_sort_idx_is_0 :
  ptec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma ptec_channel_observed_override_idx_is_1 :
  ptec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma ptec_channel_class9_pt_exception_continuum_idx_is_2 :
  ptec_channel_dblock_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition ptec_channel_bundle : Type := nat -> ptec_channel_slot.

Definition ptExceptionContinuumBundleAllUnwired : ptec_channel_bundle :=
  fun _ => ptec_slot_unwired.

Definition ptExceptionContinuumBundleAt (b : ptec_channel_bundle) (idx : nat)
  (slot : ptec_channel_slot) : ptec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition ptExceptionContinuumBundleWithPresent
  (b : ptec_channel_bundle) (idx : nat) : ptec_channel_bundle :=
  ptExceptionContinuumBundleAt b idx ptec_slot_present.

Fixpoint count_ptec_present_up_to (b : ptec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if ptec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_ptec_present_up_to b i + add
  end.

Definition ptExceptionContinuumBundlePresentCount (b : ptec_channel_bundle) : nat :=
  count_ptec_present_up_to b ptExceptionContinuumProductChannelCount.

Definition ptExceptionContinuumBundleHolds (b : ptec_channel_bundle) (idx : nat) : bool :=
  ptec_channel_slot_is_present (b idx).

Definition ptExceptionContinuumBundleIsConcurrentProduct (b : ptec_channel_bundle) : bool :=
  Nat.leb 2 (ptExceptionContinuumBundlePresentCount b).

(* Pt Z=78 interact restriction + G-min + class 14 pt_exception_continuum concurrent witness. *)
Definition ptExceptionContinuumPt78Witness : ptec_channel_bundle :=
  ptExceptionContinuumBundleWithPresent
    (ptExceptionContinuumBundleWithPresent
      (ptExceptionContinuumBundleWithPresent ptExceptionContinuumBundleAllUnwired
        ptec_channel_occupancy_engine_sort)
      ptec_channel_observed_override)
    ptec_channel_dblock_exception_continuum.

Definition ptExceptionContinuumEmptyWitness : ptec_channel_bundle :=
  ptExceptionContinuumBundleAllUnwired.

Definition ptExceptionContinuumSinglePresent : ptec_channel_bundle :=
  ptExceptionContinuumBundleWithPresent ptExceptionContinuumBundleAllUnwired
    ptec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  ptExceptionContinuumBundleHolds ptExceptionContinuumPt78Witness
    ptec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  ptExceptionContinuumBundleHolds ptExceptionContinuumPt78Witness
    ptec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_pt_exception_continuum_channel_present :
  ptExceptionContinuumBundleHolds ptExceptionContinuumPt78Witness
    ptec_channel_dblock_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  ptExceptionContinuumBundlePresentCount ptExceptionContinuumPt78Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  ptExceptionContinuumBundleIsConcurrentProduct ptExceptionContinuumPt78Witness = true.
Proof.
  unfold ptExceptionContinuumBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  ptExceptionContinuumBundlePresentCount ptExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  ptExceptionContinuumBundleIsConcurrentProduct ptExceptionContinuumEmptyWitness = false.
Proof.
  unfold ptExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  ptExceptionContinuumBundlePresentCount ptExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  ptExceptionContinuumBundleIsConcurrentProduct ptExceptionContinuumSinglePresent = false.
Proof.
  unfold ptExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ptec_xor_posture : Type :=
  | ptec_xor_exclusive
  | ptec_xor_concurrent_product.

Definition ptecXorClassifierMarker : string := "chem_l0_pt_exception_continuum_xor_classifier_v1".
Definition ptecConcurrentProductMarker : string := "chem_int_pt_exception_continuum_product_v1".

Lemma ptec_xor_marker_ne_concurrent_product_marker :
  ptecXorClassifierMarker <> ptecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition ptecXorClassifierIncompatible (claim_xor : bool)
  (b : ptec_channel_bundle) : bool :=
  claim_xor && ptExceptionContinuumBundleIsConcurrentProduct b.

Lemma ptec_xor_refuse_on_pt78_witness :
  ptecXorClassifierIncompatible true ptExceptionContinuumPt78Witness = true.
Proof.
  unfold ptecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma ptec_xor_ok_on_concurrent_product_claim :
  ptecXorClassifierIncompatible false ptExceptionContinuumPt78Witness = false.
Proof. reflexivity. Qed.

Definition ptecProductNotXor : bool :=
  ptExceptionContinuumBundleIsConcurrentProduct ptExceptionContinuumPt78Witness &&
  ptecXorClassifierIncompatible true ptExceptionContinuumPt78Witness.

Lemma ptec_product_not_xor_true : ptecProductNotXor = true.
Proof.
  unfold ptecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  ptecProductNotXor = true /\
  Nat.leb 2 (ptExceptionContinuumBundlePresentCount
    ptExceptionContinuumPt78Witness) = true /\
  ptecXorClassifierMarker <> ptecConcurrentProductMarker.
Proof.
  split.
  - apply ptec_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply ptec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive ptec_bar_presence : Type :=
  | ptec_bar_absent
  | ptec_bar_present.

Record ptec_claim_bar : Type := {
  ptec_bar_presence_field : ptec_bar_presence;
  ptec_bar_defect_total : nat
}.

Definition ptExceptionContinuumClaimBarAbsent : ptec_claim_bar :=
  {| ptec_bar_presence_field := ptec_bar_absent;
     ptec_bar_defect_total := 0 |}.

Definition ptExceptionContinuumClaimBarZeroDefect : ptec_claim_bar :=
  {| ptec_bar_presence_field := ptec_bar_present;
     ptec_bar_defect_total := 0 |}.

Definition ptec_claim_bar_zero_defect (b : ptec_claim_bar) : bool :=
  match ptec_bar_presence_field b with
  | ptec_bar_absent => false
  | ptec_bar_present => Nat.eqb (ptec_bar_defect_total b) 0
  end.

Lemma ptec_claim_bar_zero_defect_true :
  ptec_claim_bar_zero_defect ptExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma ptec_claim_bar_absent_not_zero_defect :
  ptec_claim_bar_zero_defect ptExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive ptec_conservation_verdict : Type :=
  | ptec_verdict_unwired_ok
  | ptec_verdict_named_ok
  | ptec_verdict_design_ok
  | ptec_verdict_trivial_refuse
  | ptec_verdict_xor_refuse
  | ptec_verdict_green_invent_refuse
  | ptec_verdict_proved_without_bar_refuse
  | ptec_verdict_production_wired_refuse
  | ptec_verdict_parallel_pt_exception_continuum_axiom_refuse
  | ptec_verdict_species_id_smuggle_refuse
  | ptec_verdict_extra_element_id_refuse
  | ptec_verdict_extra_pt_exception_continuum_force_refuse
  | ptec_verdict_tp_float_pin_refuse.

Definition ptec_conservation_verdict_ok (v : ptec_conservation_verdict) : bool :=
  match v with
  | ptec_verdict_unwired_ok => true
  | ptec_verdict_named_ok => true
  | ptec_verdict_design_ok => true
  | _ => false
  end.

Definition ptExceptionContinuumBundleNontrivial (b : ptec_channel_bundle) : bool :=
  Nat.ltb 0 (ptExceptionContinuumBundlePresentCount b).

Definition evaluate_pt_exception_continuum_bundle
  (m : PtExceptionContinuumModality)
  (b : ptec_channel_bundle)
  (bar : ptec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : ptec_conservation_verdict :=
  if claim_physics_green
  then ptec_verdict_green_invent_refuse
  else if claim_proved
       then ptec_verdict_proved_without_bar_refuse
       else if negb (ptExceptionContinuumBundleNontrivial b)
            then ptec_verdict_trivial_refuse
            else if ptecXorClassifierIncompatible claim_xor_classifier b
                 then ptec_verdict_xor_refuse
                 else
                   match m with
                   | pt_exception_continuum_unwired =>
                       if ptExceptionContinuumBundleIsConcurrentProduct b
                       then ptec_verdict_named_ok
                       else ptec_verdict_design_ok
                   | pt_exception_continuum_assumed
                   | pt_exception_continuum_surrogate =>
                       ptec_verdict_design_ok
                   | pt_exception_continuum_proved =>
                       ptec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_pt_exception_continuum_close
  (m : PtExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : ptec_conservation_verdict :=
  if claim_physics_green
  then ptec_verdict_green_invent_refuse
  else if claim_production_wired
  then ptec_verdict_production_wired_refuse
  else
    match m with
    | pt_exception_continuum_unwired => ptec_verdict_unwired_ok
    | pt_exception_continuum_assumed
    | pt_exception_continuum_proved
    | pt_exception_continuum_surrogate => ptec_verdict_named_ok
    end.

Definition pt_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_pt_exception_continuum_close
          pt_exception_continuum_proved claim_physics_green claim_production_wired with
  | ptec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive ptec_conservation_law : Type :=
  | ptec_law_conserved
  | ptec_law_named_ok
  | ptec_law_trivial_refuse
  | ptec_law_green_invent_refuse.

Definition ptec_conservation_law_count : nat := 4.

Lemma ptec_conservation_law_count_is_four :
  ptec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive ptec_conservation_law_witness : Type :=
  | ptec_law_witness_open
  | ptec_law_witness_proved.

Definition evaluate_ptec_conservation_law_witness
  (law : ptec_conservation_law)
  (m : PtExceptionContinuumModality)
  : ptec_conservation_law_witness :=
  match m with
  | pt_exception_continuum_unwired
  | pt_exception_continuum_assumed
  | pt_exception_continuum_surrogate => ptec_law_witness_open
  | pt_exception_continuum_proved => ptec_law_witness_proved
  end.

Lemma all_ptec_conservation_laws_open_at_unwired :
  evaluate_ptec_conservation_law_witness ptec_law_conserved
    pt_exception_continuum_unwired = ptec_law_witness_open /\
  evaluate_ptec_conservation_law_witness ptec_law_named_ok
    pt_exception_continuum_unwired = ptec_law_witness_open /\
  evaluate_ptec_conservation_law_witness ptec_law_trivial_refuse
    pt_exception_continuum_unwired = ptec_law_witness_open /\
  evaluate_ptec_conservation_law_witness ptec_law_green_invent_refuse
    pt_exception_continuum_unwired = ptec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition ptExceptionContinuumProved : bool := false.

Lemma pt_exception_continuum_proved_false :
  ptExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_unwired false false =
  ptec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_unwired false false =
  ptec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_unwired false false) =
  true.
Proof.
  unfold ptec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt78_witness_named_ok :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false false =
  ptec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_pt_exception_continuum :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false false =
  ptec_verdict_named_ok /\
  ptExceptionContinuumBundleIsConcurrentProduct ptExceptionContinuumPt78Witness = true /\
  platinum_atomic_number_z = 78 /\
  pt_observed_occupancy_tag = "5d96s1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma ptec_named_close_ok :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_proved false false =
  ptec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt_exception_continuum_close :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_proved false false =
  ptec_verdict_named_ok /\
  pt_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply ptec_named_close_ok.
  - unfold pt_exception_continuum_authorized.
    rewrite ptec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — pt_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumEmptyWitness
    ptExceptionContinuumClaimBarAbsent false false false =
  ptec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumEmptyWitness
    ptExceptionContinuumClaimBarAbsent false false false =
  ptec_verdict_trivial_refuse /\
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_bundle
       pt_exception_continuum_unwired
       ptExceptionContinuumEmptyWitness
       ptExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold ptec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent true false false =
  ptec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent true false false =
  ptec_verdict_xor_refuse /\
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_bundle
       pt_exception_continuum_unwired
       ptExceptionContinuumPt78Witness
       ptExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold ptec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_unwired true false =
  ptec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_unwired true false) =
  false.
Proof.
  unfold ptec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ptec_bundle_refuse :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false true false =
  ptec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — pt_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false true =
  ptec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false true =
  ptec_verdict_proved_without_bar_refuse /\
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_bundle
       pt_exception_continuum_unwired
       ptExceptionContinuumPt78Witness
       ptExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold ptec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — pt_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_proved false true =
  ptec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_proved false true) =
  false.
Proof.
  unfold ptec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel pt_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition ptExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelPtExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_pt_exception_continuum_axiom_refuse :
  ptExceptionContinuumAuthority <>
  parallelPtExceptionAxiomTag /\
  ptExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply pt_exception_continuum_proved_false.
Qed.

Theorem parallel_pt_exception_continuum_axiom_not_minted :
  ptExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  ptExceptionContinuumProved = false /\
  ptExceptionContinuumAuthority <> parallelPtExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "ni_z28_occupancy_copied_onto_pt_z78".

Definition ptExceptionContinuumFraming : string :=
  "second_law_conservation_pt_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  ptExceptionContinuumFraming <>
  homologCopyFraming /\
  platinum_atomic_number_z = 78 /\
  pt_observed_occupancy_tag = "5d96s1".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pt_ni_homolog_not_occupancy_copy :
  ptExceptionContinuumFraming <>
  homologCopyFraming /\
  platinum_atomic_number_z = 78 /\
  nickel_homolog_z = 28 /\
  pt_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag /\
  ptExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — pt_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "pt_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  ptExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  ptExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — pt_exception_continuum ≠ extra pt_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_pt_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/pt_exception_continuum_barrier.rs".

Lemma extra_pt_exception_continuum_force_refuse :
  ptExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem pt_exception_continuum_not_extra_pt_exception_continuum_force :
  ptExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pt_exception_continuum_barrier.rs" /\
  ptExceptionContinuumProved = false.
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
  ptExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pt_observed_occupancy_tag <> pt_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply pt_observed_ne_predicted_occupancy.
Qed.

Theorem pt_observed_override_not_madelung_family_smuggle :
  ptExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pt_observed_occupancy_tag = "5d96s1" /\
  pt_predicted_occupancy_tag = "5d8" /\
  ptExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply pt_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_pt_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  ptExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  ptExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  PtExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition ptec_conservation_coherence_scaffold : bool :=
  ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_proved false false) &&
  negb (ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_unwired true false)) &&
  negb (ptec_conservation_verdict_ok
    (evaluate_pt_exception_continuum_close
       pt_exception_continuum_proved false true)).

Lemma ptec_conservation_coherence_scaffold_true :
  ptec_conservation_coherence_scaffold = true.
Proof.
  unfold ptec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem ptec_conservation_coherence_scaffold_theorem :
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_proved false false =
    ptec_verdict_named_ok /\
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_unwired true false =
    ptec_verdict_green_invent_refuse /\
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_proved false true =
    ptec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition ptec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition ptec_conservation_knowing_fiber_ok : bool :=
  ptec_conservation_fiber_ok fiber_quantum_knowing.

Definition ptec_conservation_meso_acting_ok : bool :=
  ptec_conservation_fiber_ok fiber_meso_acting.

Lemma ptec_conservation_knowing_fiber_ok_true :
  ptec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma ptec_conservation_meso_acting_not_ok :
  ptec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem ptec_conservation_routes_knowing_not_meso :
  ptec_conservation_knowing_fiber_ok = true /\
  ptec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply ptec_conservation_knowing_fiber_ok_true.
  - apply ptec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  ptec_conservation_knowing_fiber_ok &&
  negb ptec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, ptec_conservation_knowing_fiber_ok,
    ptec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem pt_exception_continuum_fixture_scaffold :
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false false =
    ptec_verdict_named_ok /\
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumEmptyWitness
    ptExceptionContinuumClaimBarAbsent false false false =
    ptec_verdict_trivial_refuse /\
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent true false false =
    ptec_verdict_xor_refuse /\
  evaluate_pt_exception_continuum_bundle
    pt_exception_continuum_unwired
    ptExceptionContinuumPt78Witness
    ptExceptionContinuumClaimBarAbsent false false true =
    ptec_verdict_proved_without_bar_refuse /\
  evaluate_pt_exception_continuum_close
    pt_exception_continuum_unwired false false =
    ptec_verdict_unwired_ok /\
  ptec_conservation_knowing_fiber_ok = true /\
  ptec_conservation_meso_acting_ok = false /\
  ptExceptionContinuumProved = false /\
  ptecProductNotXor = true /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ni Z=28 / Pd Z=46 homolog not Pt copy — homolog ≠ identity          *)
(* ------------------------------------------------------------------ *)

Definition palladium_homolog_z : nat := 46.

Lemma palladium_homolog_z_is_46 :
  palladium_homolog_z = 46.
Proof. reflexivity. Qed.

Definition pd_homolog_observed_occupancy_tag : string := "4d105s0".

Lemma ni_pd_homolog_occupancy_tags_distinct :
  ni_homolog_observed_occupancy_tag <> pd_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma pt_ni_pd_homolog_not_copy :
  platinum_atomic_number_z = 78 /\
  nickel_homolog_z = 28 /\
  palladium_homolog_z = 46 /\
  pt_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag /\
  pt_observed_occupancy_tag <> pd_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pt_period6_homolog_not_ni_pd_occupancy_copy :
  platinum_atomic_number_z = 78 /\
  nickel_homolog_z = 28 /\
  palladium_homolog_z = 46 /\
  ni_homolog_observed_occupancy_tag = "3d84s2" /\
  pd_homolog_observed_occupancy_tag = "4d105s0" /\
  pt_observed_occupancy_tag = "5d96s1" /\
  pt_observed_occupancy_tag <> ni_homolog_observed_occupancy_tag /\
  pt_observed_occupancy_tag <> pd_homolog_observed_occupancy_tag /\
  ptExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pt_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition ptExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition ptExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-PT-EXCEPTION-CONTINUUM".

Definition ptExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PT-EXCEPTION-CONTINUUM PtExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice ptExceptionContinuumProved false evaluatePtExceptionContinuumBundle evaluatePtExceptionContinuum named Pt Z=78 NamedException occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel ni exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ni Z=28 Pd Z=46 homolog not Pt 3d8 4s2 4d10 5s0 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma pt_exception_continuum_cell_id :
  ptExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-PT-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma pt_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma pt_exception_continuum_authority_path :
  ptExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma pt_exception_continuum_cites_l0_ore02 :
  ptExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma pt_exception_continuum_cites_marker :
  ptecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma pt_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma pt_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma pt_exception_continuum_not_26th_axiom :
  ptExceptionContinuumFraming <> parallelPtExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma pt_exception_continuum_second_law_conservation_framing :
  ptExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_pt_exception_continuum_morphism".

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
  ptExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not pt_exception_continuum axiom / extra force     *)
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

Theorem pt_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pt_exception_continuum_barrier.rs" /\
  ptExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma pt_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma pt_exception_continuum_modality_unwired :
  ptExceptionContinuumModalityCurrent =
  pt_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition ptExceptionContinuumProductionWired : Prop := False.

Lemma pt_exception_continuum_not_production_wired :
  ~ ptExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


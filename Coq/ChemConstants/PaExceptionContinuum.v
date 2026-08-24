(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PaExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Pa Z=91 actinide occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Pa Z=91 5f2 6d1 7s2 actinide Madelung exception; Pr Z=59 / Th Z=90 homolog not Pa copy. *)
(*  paExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **pa_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PaExceptionContinuumModality : Type :=
  | pa_exception_continuum_unwired
  | pa_exception_continuum_assumed
  | pa_exception_continuum_proved
  | pa_exception_continuum_surrogate.

Definition paExceptionContinuumModalityCurrent :
  PaExceptionContinuumModality :=
  pa_exception_continuum_unwired.

Definition pa_exception_continuum_lattice_cardinality : nat := 4.

Lemma pa_exception_continuum_lattice_cardinality_is_four :
  pa_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma pa_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb pa_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold pa_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — pa_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_pa_exception_continuum_idx : nat := 14.

Lemma pattern_class_pa_exception_continuum_idx_is_14 :
  pattern_class_pa_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma pa_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_pa_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_pa_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_pa_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_pa_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_pa_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_pa_exception_continuum_tag_nonempty :
  pattern_class_pa_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_pa_exception_continuum_tag_nonempty :
  north_star_class_14_pa_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Pa Z=91 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition protactinium_atomic_number_z : nat := 91.

Lemma protactinium_atomic_number_z_is_91 :
  protactinium_atomic_number_z = 91.
Proof. reflexivity. Qed.

Definition protactinium_z_valid : bool :=
  Nat.ltb 0 protactinium_atomic_number_z &&
  Nat.leb protactinium_atomic_number_z iupac_table_cardinality.

Lemma protactinium_z_valid_true : protactinium_z_valid = true.
Proof.
  unfold protactinium_z_valid, protactinium_atomic_number_z, iupac_table_cardinality.
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
(*  Pa Z=91 occupancy pins — 6d¹7s² observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition pa_element_symbol : string := "Pa".

Definition pa_observed_occupancy_tag : string := "5f26d17s2".

Definition pa_predicted_occupancy_tag : string := "5f3".

Definition pa_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f26d1".

Definition pa_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f3".

Definition th_homolog_observed_occupancy_tag : string := "6d27s2".

Definition thorium_homolog_z : nat := 90.

Lemma thorium_homolog_z_is_90 :
  thorium_homolog_z = 90.
Proof. reflexivity. Qed.

Definition pr_homolog_observed_occupancy_tag : string := "6s24f3".

Definition praseodymium_homolog_z : nat := 59.

Lemma praseodymium_homolog_z_is_59 :
  praseodymium_homolog_z = 59.
Proof. reflexivity. Qed.

Lemma pa_element_symbol_nonempty :
  pa_element_symbol <> "".
Proof. discriminate. Qed.

Lemma pa_observed_occupancy_tag_nonempty :
  pa_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pa_predicted_occupancy_tag_nonempty :
  pa_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma pa_observed_ne_predicted_occupancy :
  pa_observed_occupancy_tag <> pa_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma pa_observed_ne_predicted_subshell :
  pa_observed_subshell_notation <> pa_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma pa_homolog_th_occupancy_not_copy :
  pa_observed_occupancy_tag <> th_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Lemma pa_homolog_pr_occupancy_not_copy :
  pa_observed_occupancy_tag <> pr_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "actinide_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "actinide_exception".
Proof. reflexivity. Qed.

Definition pa_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma pa_exception_continuum_factor_tag_nonempty :
  pa_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive paec_channel_slot : Type :=
  | paec_slot_unwired
  | paec_slot_absent
  | paec_slot_present.

Definition paec_channel_slot_beq (s1 s2 : paec_channel_slot) : bool :=
  match s1, s2 with
  | paec_slot_unwired, paec_slot_unwired => true
  | paec_slot_absent, paec_slot_absent => true
  | paec_slot_present, paec_slot_present => true
  | _, _ => false
  end.

Definition paec_channel_slot_is_present (s : paec_channel_slot) : bool :=
  match s with
  | paec_slot_present => true
  | _ => false
  end.

Definition paExceptionContinuumProductChannelCount : nat := 3.

Lemma pa_exception_continuum_product_channel_count_is_three :
  paExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 pa_exception_continuum. *)
Definition paec_channel_occupancy_engine_sort : nat := 0.
Definition paec_channel_observed_override : nat := 1.
Definition paec_channel_actinide_exception_continuum : nat := 2.

Lemma paec_channel_occupancy_engine_sort_idx_is_0 :
  paec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma paec_channel_observed_override_idx_is_1 :
  paec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma paec_channel_class9_pa_exception_continuum_idx_is_2 :
  paec_channel_actinide_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition paec_channel_bundle : Type := nat -> paec_channel_slot.

Definition paExceptionContinuumBundleAllUnwired : paec_channel_bundle :=
  fun _ => paec_slot_unwired.

Definition paExceptionContinuumBundleAt (b : paec_channel_bundle) (idx : nat)
  (slot : paec_channel_slot) : paec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition paExceptionContinuumBundleWithPresent
  (b : paec_channel_bundle) (idx : nat) : paec_channel_bundle :=
  paExceptionContinuumBundleAt b idx paec_slot_present.

Fixpoint count_paec_present_up_to (b : paec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if paec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_paec_present_up_to b i + add
  end.

Definition paExceptionContinuumBundlePresentCount (b : paec_channel_bundle) : nat :=
  count_paec_present_up_to b paExceptionContinuumProductChannelCount.

Definition paExceptionContinuumBundleHolds (b : paec_channel_bundle) (idx : nat) : bool :=
  paec_channel_slot_is_present (b idx).

Definition paExceptionContinuumBundleIsConcurrentProduct (b : paec_channel_bundle) : bool :=
  Nat.leb 2 (paExceptionContinuumBundlePresentCount b).

(* Pa Z=91 interact restriction + G-min + class 14 pa_exception_continuum concurrent witness. *)
Definition paExceptionContinuumPa91Witness : paec_channel_bundle :=
  paExceptionContinuumBundleWithPresent
    (paExceptionContinuumBundleWithPresent
      (paExceptionContinuumBundleWithPresent paExceptionContinuumBundleAllUnwired
        paec_channel_occupancy_engine_sort)
      paec_channel_observed_override)
    paec_channel_actinide_exception_continuum.

Definition paExceptionContinuumEmptyWitness : paec_channel_bundle :=
  paExceptionContinuumBundleAllUnwired.

Definition paExceptionContinuumSinglePresent : paec_channel_bundle :=
  paExceptionContinuumBundleWithPresent paExceptionContinuumBundleAllUnwired
    paec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  paExceptionContinuumBundleHolds paExceptionContinuumPa91Witness
    paec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  paExceptionContinuumBundleHolds paExceptionContinuumPa91Witness
    paec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_pa_exception_continuum_channel_present :
  paExceptionContinuumBundleHolds paExceptionContinuumPa91Witness
    paec_channel_actinide_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma pa91_witness_present_count_is_three :
  paExceptionContinuumBundlePresentCount paExceptionContinuumPa91Witness = 3.
Proof. reflexivity. Qed.

Lemma pa91_witness_is_concurrent_product :
  paExceptionContinuumBundleIsConcurrentProduct paExceptionContinuumPa91Witness = true.
Proof.
  unfold paExceptionContinuumBundleIsConcurrentProduct.
  rewrite pa91_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  paExceptionContinuumBundlePresentCount paExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  paExceptionContinuumBundleIsConcurrentProduct paExceptionContinuumEmptyWitness = false.
Proof.
  unfold paExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  paExceptionContinuumBundlePresentCount paExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  paExceptionContinuumBundleIsConcurrentProduct paExceptionContinuumSinglePresent = false.
Proof.
  unfold paExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive paec_xor_posture : Type :=
  | paec_xor_exclusive
  | paec_xor_concurrent_product.

Definition paecXorClassifierMarker : string := "chem_l0_pa_exception_continuum_xor_classifier_v1".
Definition paecConcurrentProductMarker : string := "chem_int_pa_exception_continuum_product_v1".

Lemma paec_xor_marker_ne_concurrent_product_marker :
  paecXorClassifierMarker <> paecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition paecXorClassifierIncompatible (claim_xor : bool)
  (b : paec_channel_bundle) : bool :=
  claim_xor && paExceptionContinuumBundleIsConcurrentProduct b.

Lemma paec_xor_refuse_on_pa91_witness :
  paecXorClassifierIncompatible true paExceptionContinuumPa91Witness = true.
Proof.
  unfold paecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma paec_xor_ok_on_concurrent_product_claim :
  paecXorClassifierIncompatible false paExceptionContinuumPa91Witness = false.
Proof. reflexivity. Qed.

Definition paecProductNotXor : bool :=
  paExceptionContinuumBundleIsConcurrentProduct paExceptionContinuumPa91Witness &&
  paecXorClassifierIncompatible true paExceptionContinuumPa91Witness.

Lemma paec_product_not_xor_true : paecProductNotXor = true.
Proof.
  unfold paecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  paecProductNotXor = true /\
  Nat.leb 2 (paExceptionContinuumBundlePresentCount
    paExceptionContinuumPa91Witness) = true /\
  paecXorClassifierMarker <> paecConcurrentProductMarker.
Proof.
  split.
  - apply paec_product_not_xor_true.
  - split.
    + rewrite pa91_witness_present_count_is_three.
      reflexivity.
    + apply paec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive paec_bar_presence : Type :=
  | paec_bar_absent
  | paec_bar_present.

Record paec_claim_bar : Type := {
  paec_bar_presence_field : paec_bar_presence;
  paec_bar_defect_total : nat
}.

Definition paExceptionContinuumClaimBarAbsent : paec_claim_bar :=
  {| paec_bar_presence_field := paec_bar_absent;
     paec_bar_defect_total := 0 |}.

Definition paExceptionContinuumClaimBarZeroDefect : paec_claim_bar :=
  {| paec_bar_presence_field := paec_bar_present;
     paec_bar_defect_total := 0 |}.

Definition paec_claim_bar_zero_defect (b : paec_claim_bar) : bool :=
  match paec_bar_presence_field b with
  | paec_bar_absent => false
  | paec_bar_present => Nat.eqb (paec_bar_defect_total b) 0
  end.

Lemma paec_claim_bar_zero_defect_true :
  paec_claim_bar_zero_defect paExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma paec_claim_bar_absent_not_zero_defect :
  paec_claim_bar_zero_defect paExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive paec_conservation_verdict : Type :=
  | paec_verdict_unwired_ok
  | paec_verdict_named_ok
  | paec_verdict_design_ok
  | paec_verdict_trivial_refuse
  | paec_verdict_xor_refuse
  | paec_verdict_green_invent_refuse
  | paec_verdict_proved_without_bar_refuse
  | paec_verdict_production_wired_refuse
  | paec_verdict_parallel_pa_exception_continuum_axiom_refuse
  | paec_verdict_species_id_smuggle_refuse
  | paec_verdict_extra_element_id_refuse
  | paec_verdict_extra_pa_exception_continuum_force_refuse
  | paec_verdict_tp_float_pin_refuse.

Definition paec_conservation_verdict_ok (v : paec_conservation_verdict) : bool :=
  match v with
  | paec_verdict_unwired_ok => true
  | paec_verdict_named_ok => true
  | paec_verdict_design_ok => true
  | _ => false
  end.

Definition paExceptionContinuumBundleNontrivial (b : paec_channel_bundle) : bool :=
  Nat.ltb 0 (paExceptionContinuumBundlePresentCount b).

Definition evaluate_pa_exception_continuum_bundle
  (m : PaExceptionContinuumModality)
  (b : paec_channel_bundle)
  (bar : paec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : paec_conservation_verdict :=
  if claim_physics_green
  then paec_verdict_green_invent_refuse
  else if claim_proved
       then paec_verdict_proved_without_bar_refuse
       else if negb (paExceptionContinuumBundleNontrivial b)
            then paec_verdict_trivial_refuse
            else if paecXorClassifierIncompatible claim_xor_classifier b
                 then paec_verdict_xor_refuse
                 else
                   match m with
                   | pa_exception_continuum_unwired =>
                       if paExceptionContinuumBundleIsConcurrentProduct b
                       then paec_verdict_named_ok
                       else paec_verdict_design_ok
                   | pa_exception_continuum_assumed
                   | pa_exception_continuum_surrogate =>
                       paec_verdict_design_ok
                   | pa_exception_continuum_proved =>
                       paec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_pa_exception_continuum_close
  (m : PaExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : paec_conservation_verdict :=
  if claim_physics_green
  then paec_verdict_green_invent_refuse
  else if claim_production_wired
  then paec_verdict_production_wired_refuse
  else
    match m with
    | pa_exception_continuum_unwired => paec_verdict_unwired_ok
    | pa_exception_continuum_assumed
    | pa_exception_continuum_proved
    | pa_exception_continuum_surrogate => paec_verdict_named_ok
    end.

Definition pa_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_pa_exception_continuum_close
          pa_exception_continuum_proved claim_physics_green claim_production_wired with
  | paec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive paec_conservation_law : Type :=
  | paec_law_conserved
  | paec_law_named_ok
  | paec_law_trivial_refuse
  | paec_law_green_invent_refuse.

Definition paec_conservation_law_count : nat := 4.

Lemma paec_conservation_law_count_is_four :
  paec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive paec_conservation_law_witness : Type :=
  | paec_law_witness_open
  | paec_law_witness_proved.

Definition evaluate_paec_conservation_law_witness
  (law : paec_conservation_law)
  (m : PaExceptionContinuumModality)
  : paec_conservation_law_witness :=
  match m with
  | pa_exception_continuum_unwired
  | pa_exception_continuum_assumed
  | pa_exception_continuum_surrogate => paec_law_witness_open
  | pa_exception_continuum_proved => paec_law_witness_proved
  end.

Lemma all_paec_conservation_laws_open_at_unwired :
  evaluate_paec_conservation_law_witness paec_law_conserved
    pa_exception_continuum_unwired = paec_law_witness_open /\
  evaluate_paec_conservation_law_witness paec_law_named_ok
    pa_exception_continuum_unwired = paec_law_witness_open /\
  evaluate_paec_conservation_law_witness paec_law_trivial_refuse
    pa_exception_continuum_unwired = paec_law_witness_open /\
  evaluate_paec_conservation_law_witness paec_law_green_invent_refuse
    pa_exception_continuum_unwired = paec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition paExceptionContinuumProved : bool := false.

Lemma pa_exception_continuum_proved_false :
  paExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_unwired false false =
  paec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_unwired false false =
  paec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_unwired false false) =
  true.
Proof.
  unfold paec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pa Z=91 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pa91_witness_named_ok :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false false =
  paec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pa91_pa_exception_continuum :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false false =
  paec_verdict_named_ok /\
  paExceptionContinuumBundleIsConcurrentProduct paExceptionContinuumPa91Witness = true /\
  protactinium_atomic_number_z = 91 /\
  pa_observed_occupancy_tag = "5f26d17s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma paec_named_close_ok :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_proved false false =
  paec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pa_exception_continuum_close :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_proved false false =
  paec_verdict_named_ok /\
  pa_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply paec_named_close_ok.
  - unfold pa_exception_continuum_authorized.
    rewrite paec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — pa_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumEmptyWitness
    paExceptionContinuumClaimBarAbsent false false false =
  paec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumEmptyWitness
    paExceptionContinuumClaimBarAbsent false false false =
  paec_verdict_trivial_refuse /\
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_bundle
       pa_exception_continuum_unwired
       paExceptionContinuumEmptyWitness
       paExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold paec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent true false false =
  paec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent true false false =
  paec_verdict_xor_refuse /\
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_bundle
       pa_exception_continuum_unwired
       paExceptionContinuumPa91Witness
       paExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold paec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_unwired true false =
  paec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_unwired true false) =
  false.
Proof.
  unfold paec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_paec_bundle_refuse :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false true false =
  paec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — pa_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false true =
  paec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false true =
  paec_verdict_proved_without_bar_refuse /\
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_bundle
       pa_exception_continuum_unwired
       paExceptionContinuumPa91Witness
       paExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold paec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — pa_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_proved false true =
  paec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_proved false true) =
  false.
Proof.
  unfold paec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel pa_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition paExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelPaExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_pa_exception_continuum_axiom_refuse :
  paExceptionContinuumAuthority <>
  parallelPaExceptionAxiomTag /\
  paExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply pa_exception_continuum_proved_false.
Qed.

Theorem parallel_pa_exception_continuum_axiom_not_minted :
  paExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  paExceptionContinuumProved = false /\
  paExceptionContinuumAuthority <> parallelPaExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "pr_th_z59_z90_occupancy_copied_onto_pa_z91".

Definition paExceptionContinuumFraming : string :=
  "second_law_conservation_pa_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  paExceptionContinuumFraming <>
  homologCopyFraming /\
  protactinium_atomic_number_z = 91 /\
  pa_observed_occupancy_tag = "5f26d17s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pa_pr_th_homolog_not_occupancy_copy :
  paExceptionContinuumFraming <>
  homologCopyFraming /\
  protactinium_atomic_number_z = 91 /\
  praseodymium_homolog_z = 59 /\
  thorium_homolog_z = 90 /\
  pa_observed_occupancy_tag <> pr_homolog_observed_occupancy_tag /\
  pa_observed_occupancy_tag <> th_homolog_observed_occupancy_tag /\
  paExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — pa_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "pa_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  paExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  paExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  protactinium_atomic_number_z = 91.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — pa_exception_continuum ≠ extra pa_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_pa_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/pa_exception_continuum_barrier.rs".

Lemma extra_pa_exception_continuum_force_refuse :
  paExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem pa_exception_continuum_not_extra_pa_exception_continuum_force :
  paExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pa_exception_continuum_barrier.rs" /\
  paExceptionContinuumProved = false.
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
  paExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pa_observed_occupancy_tag <> pa_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply pa_observed_ne_predicted_occupancy.
Qed.

Theorem pa_observed_override_not_madelung_family_smuggle :
  paExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  pa_observed_occupancy_tag = "5f26d17s2" /\
  pa_predicted_occupancy_tag = "5f3" /\
  paExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply pa_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_pa_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  paExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  paExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  protactinium_atomic_number_z = 91.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  PaExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition paec_conservation_coherence_scaffold : bool :=
  paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_proved false false) &&
  negb (paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_unwired true false)) &&
  negb (paec_conservation_verdict_ok
    (evaluate_pa_exception_continuum_close
       pa_exception_continuum_proved false true)).

Lemma paec_conservation_coherence_scaffold_true :
  paec_conservation_coherence_scaffold = true.
Proof.
  unfold paec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem paec_conservation_coherence_scaffold_theorem :
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_proved false false =
    paec_verdict_named_ok /\
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_unwired true false =
    paec_verdict_green_invent_refuse /\
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_proved false true =
    paec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition paec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition paec_conservation_knowing_fiber_ok : bool :=
  paec_conservation_fiber_ok fiber_quantum_knowing.

Definition paec_conservation_meso_acting_ok : bool :=
  paec_conservation_fiber_ok fiber_meso_acting.

Lemma paec_conservation_knowing_fiber_ok_true :
  paec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma paec_conservation_meso_acting_not_ok :
  paec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem paec_conservation_routes_knowing_not_meso :
  paec_conservation_knowing_fiber_ok = true /\
  paec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply paec_conservation_knowing_fiber_ok_true.
  - apply paec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  paec_conservation_knowing_fiber_ok &&
  negb paec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, paec_conservation_knowing_fiber_ok,
    paec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem pa_exception_continuum_fixture_scaffold :
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false false =
    paec_verdict_named_ok /\
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumEmptyWitness
    paExceptionContinuumClaimBarAbsent false false false =
    paec_verdict_trivial_refuse /\
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent true false false =
    paec_verdict_xor_refuse /\
  evaluate_pa_exception_continuum_bundle
    pa_exception_continuum_unwired
    paExceptionContinuumPa91Witness
    paExceptionContinuumClaimBarAbsent false false true =
    paec_verdict_proved_without_bar_refuse /\
  evaluate_pa_exception_continuum_close
    pa_exception_continuum_unwired false false =
    paec_verdict_unwired_ok /\
  paec_conservation_knowing_fiber_ok = true /\
  paec_conservation_meso_acting_ok = false /\
  paExceptionContinuumProved = false /\
  paecProductNotXor = true /\
  protactinium_atomic_number_z = 91.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pr Z=59 / Th Z=90 homolog not Pa copy — period-6/7 homolog ≠ identity *)
(* ------------------------------------------------------------------ *)

Definition praseodymium_atomic_number_z : nat := 59.

Lemma praseodymium_atomic_number_z_is_59 :
  praseodymium_atomic_number_z = 59.
Proof. reflexivity. Qed.

Definition thorium_atomic_number_z : nat := 90.

Lemma thorium_atomic_number_z_is_90 :
  thorium_atomic_number_z = 90.
Proof. reflexivity. Qed.

Definition praseodymium_occupancy_tag : string := "6s24f3".

Definition thorium_occupancy_tag : string := "6d27s2".

Definition protactinium_occupancy_tag : string := "5f26d17s2".

Lemma praseodymium_protactinium_occupancy_tags_distinct :
  praseodymium_occupancy_tag <> protactinium_occupancy_tag.
Proof. discriminate. Qed.

Lemma thorium_protactinium_occupancy_tags_distinct :
  thorium_occupancy_tag <> protactinium_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma pr_th_pa_homolog_not_copy :
  protactinium_atomic_number_z = 91 /\
  praseodymium_atomic_number_z = 59 /\
  thorium_atomic_number_z = 90 /\
  praseodymium_occupancy_tag <> protactinium_occupancy_tag /\
  thorium_occupancy_tag <> protactinium_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem pr_th_period_homolog_not_pa_occupancy_copy :
  protactinium_atomic_number_z = 91 /\
  praseodymium_atomic_number_z = 59 /\
  thorium_atomic_number_z = 90 /\
  praseodymium_occupancy_tag = "6s24f3" /\
  thorium_occupancy_tag = "6d27s2" /\
  protactinium_occupancy_tag = "5f26d17s2" /\
  praseodymium_occupancy_tag <> protactinium_occupancy_tag /\
  thorium_occupancy_tag <> protactinium_occupancy_tag /\
  paExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pa_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition paExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition actinideOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition paExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-PA-EXCEPTION-CONTINUUM".

Definition paExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PA-EXCEPTION-CONTINUUM PaExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice paExceptionContinuumProved false evaluate_pa_exception_continuum_bundle evaluate_pa_exception_continuum named Pa Z=91 actinide occupancy exception continuum X29 occupancy engine sort observed override actinide exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel pa exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Pr Z=59 Th Z=90 homolog not Pa 6s24f3 6d27s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma pa_exception_continuum_cell_id :
  paExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-PA-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma pa_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma pa_exception_continuum_authority_path :
  paExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma pa_exception_continuum_cites_l0_ore02 :
  paExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma pa_exception_continuum_cites_marker :
  paecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma pa_exception_continuum_cites_pattern_product :
  actinideOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma pa_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma pa_exception_continuum_not_26th_axiom :
  paExceptionContinuumFraming <> parallelPaExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma pa_exception_continuum_second_law_conservation_framing :
  paExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition actinideExceptionNamedObject : string :=
  "interact_restriction_on_pa_exception_continuum_morphism".

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
  paExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not pa_exception_continuum axiom / extra force     *)
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

Theorem pa_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/pa_exception_continuum_barrier.rs" /\
  paExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma pa_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma pa_exception_continuum_modality_unwired :
  paExceptionContinuumModalityCurrent =
  pa_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition paExceptionContinuumProductionWired : Prop := False.

Lemma pa_exception_continuum_not_production_wired :
  ~ paExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


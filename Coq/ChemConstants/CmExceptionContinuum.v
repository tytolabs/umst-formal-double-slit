(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CmExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Cm Z=96 actinide occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Cm Z=96 5f7 6d1 7s2 actinide Madelung exception; Gd Z=64 homolog not Cm copy. *)
(*  cmExceptionContinuumProved false. Modality Unwired.               *)
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
(*  Class-14 **cm_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive CmExceptionContinuumModality : Type :=
  | cm_exception_continuum_unwired
  | cm_exception_continuum_assumed
  | cm_exception_continuum_proved
  | cm_exception_continuum_surrogate.

Definition cmExceptionContinuumModalityCurrent :
  CmExceptionContinuumModality :=
  cm_exception_continuum_unwired.

Definition cm_exception_continuum_lattice_cardinality : nat := 4.

Lemma cm_exception_continuum_lattice_cardinality_is_four :
  cm_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma cm_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb cm_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold cm_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — cm_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_cm_exception_continuum_idx : nat := 14.

Lemma pattern_class_cm_exception_continuum_idx_is_14 :
  pattern_class_cm_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma cm_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_cm_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_cm_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_cm_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_cm_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_cm_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_cm_exception_continuum_tag_nonempty :
  pattern_class_cm_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_cm_exception_continuum_tag_nonempty :
  north_star_class_14_cm_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Cm Z=96 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition curium_atomic_number_z : nat := 96.

Lemma curium_atomic_number_z_is_96 :
  curium_atomic_number_z = 96.
Proof. reflexivity. Qed.

Definition curium_z_valid : bool :=
  Nat.ltb 0 curium_atomic_number_z &&
  Nat.leb curium_atomic_number_z iupac_table_cardinality.

Lemma curium_z_valid_true : curium_z_valid = true.
Proof.
  unfold curium_z_valid, curium_atomic_number_z, iupac_table_cardinality.
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
(*  Cm Z=96 occupancy pins — 4d⁵5s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition cm_element_symbol : string := "Cm".

Definition cm_observed_occupancy_tag : string := "5f76d17s2".

Definition cm_predicted_occupancy_tag : string := "5f87s2".

Definition cm_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1".

Definition cm_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8".

Definition gd_homolog_observed_occupancy_tag : string := "4f75d16s2".

Definition gadolinium_homolog_z : nat := 64.

Lemma gadolinium_homolog_z_is_64 :
  gadolinium_homolog_z = 64.
Proof. reflexivity. Qed.

Lemma cm_element_symbol_nonempty :
  cm_element_symbol <> "".
Proof. discriminate. Qed.

Lemma cm_observed_occupancy_tag_nonempty :
  cm_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma cm_predicted_occupancy_tag_nonempty :
  cm_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma cm_observed_ne_predicted_occupancy :
  cm_observed_occupancy_tag <> cm_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma cm_observed_ne_predicted_subshell :
  cm_observed_subshell_notation <> cm_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma cm_homolog_occupancy_not_copy :
  cm_observed_occupancy_tag <> gd_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "actinide_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "actinide_exception".
Proof. reflexivity. Qed.

Definition cm_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma cm_exception_continuum_factor_tag_nonempty :
  cm_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive cmec_channel_slot : Type :=
  | cmec_slot_unwired
  | cmec_slot_absent
  | cmec_slot_present.

Definition cmec_channel_slot_beq (s1 s2 : cmec_channel_slot) : bool :=
  match s1, s2 with
  | cmec_slot_unwired, cmec_slot_unwired => true
  | cmec_slot_absent, cmec_slot_absent => true
  | cmec_slot_present, cmec_slot_present => true
  | _, _ => false
  end.

Definition cmec_channel_slot_is_present (s : cmec_channel_slot) : bool :=
  match s with
  | cmec_slot_present => true
  | _ => false
  end.

Definition cmExceptionContinuumProductChannelCount : nat := 3.

Lemma cm_exception_continuum_product_channel_count_is_three :
  cmExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 cm_exception_continuum. *)
Definition cmec_channel_occupancy_engine_sort : nat := 0.
Definition cmec_channel_observed_override : nat := 1.
Definition cmec_channel_actinide_exception_continuum : nat := 2.

Lemma cmec_channel_occupancy_engine_sort_idx_is_0 :
  cmec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma cmec_channel_observed_override_idx_is_1 :
  cmec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma cmec_channel_class9_cm_exception_continuum_idx_is_2 :
  cmec_channel_actinide_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition cmec_channel_bundle : Type := nat -> cmec_channel_slot.

Definition cmExceptionContinuumBundleAllUnwired : cmec_channel_bundle :=
  fun _ => cmec_slot_unwired.

Definition cmExceptionContinuumBundleAt (b : cmec_channel_bundle) (idx : nat)
  (slot : cmec_channel_slot) : cmec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition cmExceptionContinuumBundleWithPresent
  (b : cmec_channel_bundle) (idx : nat) : cmec_channel_bundle :=
  cmExceptionContinuumBundleAt b idx cmec_slot_present.

Fixpoint count_cmec_present_up_to (b : cmec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if cmec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_cmec_present_up_to b i + add
  end.

Definition cmExceptionContinuumBundlePresentCount (b : cmec_channel_bundle) : nat :=
  count_cmec_present_up_to b cmExceptionContinuumProductChannelCount.

Definition cmExceptionContinuumBundleHolds (b : cmec_channel_bundle) (idx : nat) : bool :=
  cmec_channel_slot_is_present (b idx).

Definition cmExceptionContinuumBundleIsConcurrentProduct (b : cmec_channel_bundle) : bool :=
  Nat.leb 2 (cmExceptionContinuumBundlePresentCount b).

(* Cm Z=96 interact restriction + G-min + class 14 cm_exception_continuum concurrent witness. *)
Definition cmExceptionContinuumCm96Witness : cmec_channel_bundle :=
  cmExceptionContinuumBundleWithPresent
    (cmExceptionContinuumBundleWithPresent
      (cmExceptionContinuumBundleWithPresent cmExceptionContinuumBundleAllUnwired
        cmec_channel_occupancy_engine_sort)
      cmec_channel_observed_override)
    cmec_channel_actinide_exception_continuum.

Definition cmExceptionContinuumEmptyWitness : cmec_channel_bundle :=
  cmExceptionContinuumBundleAllUnwired.

Definition cmExceptionContinuumSinglePresent : cmec_channel_bundle :=
  cmExceptionContinuumBundleWithPresent cmExceptionContinuumBundleAllUnwired
    cmec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  cmExceptionContinuumBundleHolds cmExceptionContinuumCm96Witness
    cmec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  cmExceptionContinuumBundleHolds cmExceptionContinuumCm96Witness
    cmec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_cm_exception_continuum_channel_present :
  cmExceptionContinuumBundleHolds cmExceptionContinuumCm96Witness
    cmec_channel_actinide_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma cm96_witness_present_count_is_three :
  cmExceptionContinuumBundlePresentCount cmExceptionContinuumCm96Witness = 3.
Proof. reflexivity. Qed.

Lemma cm96_witness_is_concurrent_product :
  cmExceptionContinuumBundleIsConcurrentProduct cmExceptionContinuumCm96Witness = true.
Proof.
  unfold cmExceptionContinuumBundleIsConcurrentProduct.
  rewrite cm96_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  cmExceptionContinuumBundlePresentCount cmExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  cmExceptionContinuumBundleIsConcurrentProduct cmExceptionContinuumEmptyWitness = false.
Proof.
  unfold cmExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  cmExceptionContinuumBundlePresentCount cmExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  cmExceptionContinuumBundleIsConcurrentProduct cmExceptionContinuumSinglePresent = false.
Proof.
  unfold cmExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive cmec_xor_posture : Type :=
  | cmec_xor_exclusive
  | cmec_xor_concurrent_product.

Definition cmecXorClassifierMarker : string := "chem_l0_cm_exception_continuum_xor_classifier_v1".
Definition cmecConcurrentProductMarker : string := "chem_int_cm_exception_continuum_product_v1".

Lemma cmec_xor_marker_ne_concurrent_product_marker :
  cmecXorClassifierMarker <> cmecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition cmecXorClassifierIncompatible (claim_xor : bool)
  (b : cmec_channel_bundle) : bool :=
  claim_xor && cmExceptionContinuumBundleIsConcurrentProduct b.

Lemma cmec_xor_refuse_on_cm96_witness :
  cmecXorClassifierIncompatible true cmExceptionContinuumCm96Witness = true.
Proof.
  unfold cmecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma cmec_xor_ok_on_concurrent_product_claim :
  cmecXorClassifierIncompatible false cmExceptionContinuumCm96Witness = false.
Proof. reflexivity. Qed.

Definition cmecProductNotXor : bool :=
  cmExceptionContinuumBundleIsConcurrentProduct cmExceptionContinuumCm96Witness &&
  cmecXorClassifierIncompatible true cmExceptionContinuumCm96Witness.

Lemma cmec_product_not_xor_true : cmecProductNotXor = true.
Proof.
  unfold cmecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  cmecProductNotXor = true /\
  Nat.leb 2 (cmExceptionContinuumBundlePresentCount
    cmExceptionContinuumCm96Witness) = true /\
  cmecXorClassifierMarker <> cmecConcurrentProductMarker.
Proof.
  split.
  - apply cmec_product_not_xor_true.
  - split.
    + rewrite cm96_witness_present_count_is_three.
      reflexivity.
    + apply cmec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive cmec_bar_presence : Type :=
  | cmec_bar_absent
  | cmec_bar_present.

Record cmec_claim_bar : Type := {
  cmec_bar_presence_field : cmec_bar_presence;
  cmec_bar_defect_total : nat
}.

Definition cmExceptionContinuumClaimBarAbsent : cmec_claim_bar :=
  {| cmec_bar_presence_field := cmec_bar_absent;
     cmec_bar_defect_total := 0 |}.

Definition cmExceptionContinuumClaimBarZeroDefect : cmec_claim_bar :=
  {| cmec_bar_presence_field := cmec_bar_present;
     cmec_bar_defect_total := 0 |}.

Definition cmec_claim_bar_zero_defect (b : cmec_claim_bar) : bool :=
  match cmec_bar_presence_field b with
  | cmec_bar_absent => false
  | cmec_bar_present => Nat.eqb (cmec_bar_defect_total b) 0
  end.

Lemma cmec_claim_bar_zero_defect_true :
  cmec_claim_bar_zero_defect cmExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma cmec_claim_bar_absent_not_zero_defect :
  cmec_claim_bar_zero_defect cmExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive cmec_conservation_verdict : Type :=
  | cmec_verdict_unwired_ok
  | cmec_verdict_named_ok
  | cmec_verdict_design_ok
  | cmec_verdict_trivial_refuse
  | cmec_verdict_xor_refuse
  | cmec_verdict_green_invent_refuse
  | cmec_verdict_proved_without_bar_refuse
  | cmec_verdict_production_wired_refuse
  | cmec_verdict_parallel_cm_exception_continuum_axiom_refuse
  | cmec_verdict_species_id_smuggle_refuse
  | cmec_verdict_extra_element_id_refuse
  | cmec_verdict_extra_cm_exception_continuum_force_refuse
  | cmec_verdict_tp_float_pin_refuse.

Definition cmec_conservation_verdict_ok (v : cmec_conservation_verdict) : bool :=
  match v with
  | cmec_verdict_unwired_ok => true
  | cmec_verdict_named_ok => true
  | cmec_verdict_design_ok => true
  | _ => false
  end.

Definition cmExceptionContinuumBundleNontrivial (b : cmec_channel_bundle) : bool :=
  Nat.ltb 0 (cmExceptionContinuumBundlePresentCount b).

Definition evaluate_cm_exception_continuum_bundle
  (m : CmExceptionContinuumModality)
  (b : cmec_channel_bundle)
  (bar : cmec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : cmec_conservation_verdict :=
  if claim_physics_green
  then cmec_verdict_green_invent_refuse
  else if claim_proved
       then cmec_verdict_proved_without_bar_refuse
       else if negb (cmExceptionContinuumBundleNontrivial b)
            then cmec_verdict_trivial_refuse
            else if cmecXorClassifierIncompatible claim_xor_classifier b
                 then cmec_verdict_xor_refuse
                 else
                   match m with
                   | cm_exception_continuum_unwired =>
                       if cmExceptionContinuumBundleIsConcurrentProduct b
                       then cmec_verdict_named_ok
                       else cmec_verdict_design_ok
                   | cm_exception_continuum_assumed
                   | cm_exception_continuum_surrogate =>
                       cmec_verdict_design_ok
                   | cm_exception_continuum_proved =>
                       cmec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_cm_exception_continuum_close
  (m : CmExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : cmec_conservation_verdict :=
  if claim_physics_green
  then cmec_verdict_green_invent_refuse
  else if claim_production_wired
  then cmec_verdict_production_wired_refuse
  else
    match m with
    | cm_exception_continuum_unwired => cmec_verdict_unwired_ok
    | cm_exception_continuum_assumed
    | cm_exception_continuum_proved
    | cm_exception_continuum_surrogate => cmec_verdict_named_ok
    end.

Definition cm_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_cm_exception_continuum_close
          cm_exception_continuum_proved claim_physics_green claim_production_wired with
  | cmec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive cmec_conservation_law : Type :=
  | cmec_law_conserved
  | cmec_law_named_ok
  | cmec_law_trivial_refuse
  | cmec_law_green_invent_refuse.

Definition cmec_conservation_law_count : nat := 4.

Lemma cmec_conservation_law_count_is_four :
  cmec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive cmec_conservation_law_witness : Type :=
  | cmec_law_witness_open
  | cmec_law_witness_proved.

Definition evaluate_cmec_conservation_law_witness
  (law : cmec_conservation_law)
  (m : CmExceptionContinuumModality)
  : cmec_conservation_law_witness :=
  match m with
  | cm_exception_continuum_unwired
  | cm_exception_continuum_assumed
  | cm_exception_continuum_surrogate => cmec_law_witness_open
  | cm_exception_continuum_proved => cmec_law_witness_proved
  end.

Lemma all_cmec_conservation_laws_open_at_unwired :
  evaluate_cmec_conservation_law_witness cmec_law_conserved
    cm_exception_continuum_unwired = cmec_law_witness_open /\
  evaluate_cmec_conservation_law_witness cmec_law_named_ok
    cm_exception_continuum_unwired = cmec_law_witness_open /\
  evaluate_cmec_conservation_law_witness cmec_law_trivial_refuse
    cm_exception_continuum_unwired = cmec_law_witness_open /\
  evaluate_cmec_conservation_law_witness cmec_law_green_invent_refuse
    cm_exception_continuum_unwired = cmec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition cmExceptionContinuumProved : bool := false.

Lemma cm_exception_continuum_proved_false :
  cmExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_unwired false false =
  cmec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_unwired false false =
  cmec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_unwired false false) =
  true.
Proof.
  unfold cmec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Cm Z=96 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma cm96_witness_named_ok :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false false =
  cmec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cm96_cm_exception_continuum :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false false =
  cmec_verdict_named_ok /\
  cmExceptionContinuumBundleIsConcurrentProduct cmExceptionContinuumCm96Witness = true /\
  curium_atomic_number_z = 96 /\
  cm_observed_occupancy_tag = "5f76d17s2".
Proof.
  repeat split; reflexivity.
Qed.

Lemma cmec_named_close_ok :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_proved false false =
  cmec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cm_exception_continuum_close :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_proved false false =
  cmec_verdict_named_ok /\
  cm_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply cmec_named_close_ok.
  - unfold cm_exception_continuum_authorized.
    rewrite cmec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — cm_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumEmptyWitness
    cmExceptionContinuumClaimBarAbsent false false false =
  cmec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumEmptyWitness
    cmExceptionContinuumClaimBarAbsent false false false =
  cmec_verdict_trivial_refuse /\
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_bundle
       cm_exception_continuum_unwired
       cmExceptionContinuumEmptyWitness
       cmExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold cmec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent true false false =
  cmec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent true false false =
  cmec_verdict_xor_refuse /\
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_bundle
       cm_exception_continuum_unwired
       cmExceptionContinuumCm96Witness
       cmExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold cmec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_unwired true false =
  cmec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_unwired true false) =
  false.
Proof.
  unfold cmec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_cmec_bundle_refuse :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false true false =
  cmec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — cm_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false true =
  cmec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false true =
  cmec_verdict_proved_without_bar_refuse /\
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_bundle
       cm_exception_continuum_unwired
       cmExceptionContinuumCm96Witness
       cmExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold cmec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — cm_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_proved false true =
  cmec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_proved false true) =
  false.
Proof.
  unfold cmec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel cm_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition cmExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelCmExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_cm_exception_continuum_axiom_refuse :
  cmExceptionContinuumAuthority <>
  parallelCmExceptionAxiomTag /\
  cmExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply cm_exception_continuum_proved_false.
Qed.

Theorem parallel_cm_exception_continuum_axiom_not_minted :
  cmExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  cmExceptionContinuumProved = false /\
  cmExceptionContinuumAuthority <> parallelCmExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "gd_z64_occupancy_copied_onto_cm_z96".

Definition cmExceptionContinuumFraming : string :=
  "second_law_conservation_cm_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  cmExceptionContinuumFraming <>
  homologCopyFraming /\
  curium_atomic_number_z = 96 /\
  cm_observed_occupancy_tag = "5f76d17s2".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem cm_gd_homolog_not_occupancy_copy :
  cmExceptionContinuumFraming <>
  homologCopyFraming /\
  curium_atomic_number_z = 96 /\
  gadolinium_homolog_z = 64 /\
  cm_observed_occupancy_tag <> gd_homolog_observed_occupancy_tag /\
  cmExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — cm_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "cm_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  cmExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  cmExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  curium_atomic_number_z = 96.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — cm_exception_continuum ≠ extra cm_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_cm_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/cm_exception_continuum_barrier.rs".

Lemma extra_cm_exception_continuum_force_refuse :
  cmExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem cm_exception_continuum_not_extra_cm_exception_continuum_force :
  cmExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/cm_exception_continuum_barrier.rs" /\
  cmExceptionContinuumProved = false.
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
  cmExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  cm_observed_occupancy_tag <> cm_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply cm_observed_ne_predicted_occupancy.
Qed.

Theorem cm_observed_override_not_madelung_family_smuggle :
  cmExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  cm_observed_occupancy_tag = "5f76d17s2" /\
  cm_predicted_occupancy_tag = "5f87s2" /\
  cmExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply cm_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_cm_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  cmExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  cmExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  curium_atomic_number_z = 96.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  CmExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition cmec_conservation_coherence_scaffold : bool :=
  cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_proved false false) &&
  negb (cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_unwired true false)) &&
  negb (cmec_conservation_verdict_ok
    (evaluate_cm_exception_continuum_close
       cm_exception_continuum_proved false true)).

Lemma cmec_conservation_coherence_scaffold_true :
  cmec_conservation_coherence_scaffold = true.
Proof.
  unfold cmec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cmec_conservation_coherence_scaffold_theorem :
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_proved false false =
    cmec_verdict_named_ok /\
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_unwired true false =
    cmec_verdict_green_invent_refuse /\
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_proved false true =
    cmec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition cmec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition cmec_conservation_knowing_fiber_ok : bool :=
  cmec_conservation_fiber_ok fiber_quantum_knowing.

Definition cmec_conservation_meso_acting_ok : bool :=
  cmec_conservation_fiber_ok fiber_meso_acting.

Lemma cmec_conservation_knowing_fiber_ok_true :
  cmec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma cmec_conservation_meso_acting_not_ok :
  cmec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem cmec_conservation_routes_knowing_not_meso :
  cmec_conservation_knowing_fiber_ok = true /\
  cmec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply cmec_conservation_knowing_fiber_ok_true.
  - apply cmec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  cmec_conservation_knowing_fiber_ok &&
  negb cmec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, cmec_conservation_knowing_fiber_ok,
    cmec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem cm_exception_continuum_fixture_scaffold :
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false false =
    cmec_verdict_named_ok /\
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumEmptyWitness
    cmExceptionContinuumClaimBarAbsent false false false =
    cmec_verdict_trivial_refuse /\
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent true false false =
    cmec_verdict_xor_refuse /\
  evaluate_cm_exception_continuum_bundle
    cm_exception_continuum_unwired
    cmExceptionContinuumCm96Witness
    cmExceptionContinuumClaimBarAbsent false false true =
    cmec_verdict_proved_without_bar_refuse /\
  evaluate_cm_exception_continuum_close
    cm_exception_continuum_unwired false false =
    cmec_verdict_unwired_ok /\
  cmec_conservation_knowing_fiber_ok = true /\
  cmec_conservation_meso_acting_ok = false /\
  cmExceptionContinuumProved = false /\
  cmecProductNotXor = true /\
  curium_atomic_number_z = 96.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Gd Z=64 homolog not Cm copy — period-6 f-block homolog ≠ identity  *)
(* ------------------------------------------------------------------ *)

Definition gadolinium_atomic_number_z : nat := 64.

Lemma gadolinium_atomic_number_z_is_64 :
  gadolinium_atomic_number_z = 64.
Proof. reflexivity. Qed.

Definition gadolinium_homolog_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1".

Lemma gd_homolog_occupancy_tag_named :
  gd_homolog_observed_occupancy_tag = "4f75d16s2".
Proof. reflexivity. Qed.

Lemma cm_gd_homolog_subshell_not_copy :
  cm_observed_subshell_notation <>
  gadolinium_homolog_observed_subshell_notation.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma cm_gd_homolog_not_copy :
  curium_atomic_number_z = 96 /\
  gadolinium_atomic_number_z = 64 /\
  cm_observed_occupancy_tag <> gd_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem gd_period6_homolog_not_cm_occupancy_copy :
  curium_atomic_number_z = 96 /\
  gadolinium_atomic_number_z = 64 /\
  cm_observed_occupancy_tag = "5f76d17s2" /\
  gd_homolog_observed_occupancy_tag = "4f75d16s2" /\
  cm_observed_occupancy_tag <> gd_homolog_observed_occupancy_tag /\
  cmExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — cm_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition cmExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition cmExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-CM-EXCEPTION-CONTINUUM".

Definition cmExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CM-EXCEPTION-CONTINUUM CmExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice cmExceptionContinuumProved false evaluateCmExceptionContinuumBundle evaluateCmExceptionContinuum named Cm Z=96 actinide occupancy exception continuum X29 occupancy engine sort observed override actinide exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Gd Z=64 homolog not Cm 4f7 5d1 6s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma cm_exception_continuum_cell_id :
  cmExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-CM-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma cm_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma cm_exception_continuum_authority_path :
  cmExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma cm_exception_continuum_cites_l0_ore02 :
  cmExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma cm_exception_continuum_cites_marker :
  cmecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma cm_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma cm_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma cm_exception_continuum_not_26th_axiom :
  cmExceptionContinuumFraming <> parallelCmExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma cm_exception_continuum_second_law_conservation_framing :
  cmExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition actinideExceptionNamedObject : string :=
  "interact_restriction_on_cm_exception_continuum_morphism".

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
  cmExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not cm_exception_continuum axiom / extra force     *)
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

Theorem cm_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/cm_exception_continuum_barrier.rs" /\
  cmExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma cm_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma cm_exception_continuum_modality_unwired :
  cmExceptionContinuumModalityCurrent =
  cm_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition cmExceptionContinuumProductionWired : Prop := False.

Lemma cm_exception_continuum_not_production_wired :
  ~ cmExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.


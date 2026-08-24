(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CatalysisConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 14 **catalysis** **conservation**.        *)
(*  Catalysis is an **Interact restriction** on the same second-law +  *)
(*  conservation object (not a catalysis axiom / extra force).         *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  TST is prior art; the named object is the restriction.             *)
(*  catalysisConservationProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/catalysis_barrier.rs (read-only cite).     *)
(*  INT: umst/umst-chem/src/l0_tables/catalysis.rs (read-only cite).   *)
(*  INT: umst/umst-chem/src/interact_partiality.rs (read-only cite).   *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **catalysis** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive CatalysisConservationModality : Type :=
  | catalysis_conservation_unwired
  | catalysis_conservation_assumed
  | catalysis_conservation_proved
  | catalysis_conservation_surrogate.

Definition catalysisConservationModalityCurrent :
  CatalysisConservationModality :=
  catalysis_conservation_unwired.

Definition catalysis_lattice_cardinality : nat := 4.

Lemma catalysis_lattice_cardinality_is_four :
  catalysis_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma catalysis_lattice_not_118_squared :
  negb (Nat.eqb catalysis_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold catalysis_lattice_cardinality.
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

(* North-star §2 class 14 — catalysis concurrent Π_c factor. *)
Definition pattern_class_catalysis_idx : nat := 14.

Lemma pattern_class_catalysis_idx_is_14 :
  pattern_class_catalysis_idx = 14.
Proof. reflexivity. Qed.

Lemma catalysis_class_index_valid :
  pattern_class_index_valid pattern_class_catalysis_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_catalysis_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierCatalysisRowId : string := "X14".

Lemma cross_classifier_catalysis_row_named :
  crossClassifierCatalysisRowId = "X14".
Proof. reflexivity. Qed.

Definition pattern_class_catalysis_tag : string :=
  "catalysis".

Definition north_star_class_14_catalysis_tag : string :=
  "class 14 catalysis".

Lemma pattern_class_catalysis_tag_nonempty :
  pattern_class_catalysis_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_catalysis_tag_nonempty :
  north_star_class_14_catalysis_tag <> "".
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

Definition catalysis_factor_tag : string :=
  "catalysis".

Definition interact_restriction_channel_tag : string := "interact_restriction".

Definition tst_prior_art_channel_tag : string := "tst_prior_art".

Lemma catalysis_factor_tag_nonempty :
  catalysis_factor_tag <> "".
Proof. discriminate. Qed.

Lemma interact_restriction_channel_tag_nonempty :
  interact_restriction_channel_tag <> "".
Proof. discriminate. Qed.

Lemma tst_prior_art_channel_tag_nonempty :
  tst_prior_art_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive ccv_channel_slot : Type :=
  | ccv_slot_unwired
  | ccv_slot_absent
  | ccv_slot_present.

Definition ccv_channel_slot_beq (s1 s2 : ccv_channel_slot) : bool :=
  match s1, s2 with
  | ccv_slot_unwired, ccv_slot_unwired => true
  | ccv_slot_absent, ccv_slot_absent => true
  | ccv_slot_present, ccv_slot_present => true
  | _, _ => false
  end.

Definition ccv_channel_slot_is_present (s : ccv_channel_slot) : bool :=
  match s with
  | ccv_slot_present => true
  | _ => false
  end.

Definition catalysisProductChannelCount : nat := 3.

Lemma catalysis_product_channel_count_is_three :
  catalysisProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 catalysis. *)
Definition ccv_channel_interact_restriction : nat := 0.
Definition ccv_channel_tst_prior_art : nat := 1.
Definition ccv_channel_class9_catalysis : nat := 2.

Lemma ccv_channel_interact_restriction_idx_is_0 :
  ccv_channel_interact_restriction = 0.
Proof. reflexivity. Qed.

Lemma ccv_channel_tst_prior_art_idx_is_1 :
  ccv_channel_tst_prior_art = 1.
Proof. reflexivity. Qed.

Lemma ccv_channel_class9_catalysis_idx_is_2 :
  ccv_channel_class9_catalysis = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition ccv_channel_bundle : Type := nat -> ccv_channel_slot.

Definition catalysisBundleAllUnwired : ccv_channel_bundle :=
  fun _ => ccv_slot_unwired.

Definition catalysisBundleAt (b : ccv_channel_bundle) (idx : nat)
  (slot : ccv_channel_slot) : ccv_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition catalysisBundleWithPresent
  (b : ccv_channel_bundle) (idx : nat) : ccv_channel_bundle :=
  catalysisBundleAt b idx ccv_slot_present.

Fixpoint count_ccv_present_up_to (b : ccv_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if ccv_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_ccv_present_up_to b i + add
  end.

Definition catalysisBundlePresentCount (b : ccv_channel_bundle) : nat :=
  count_ccv_present_up_to b catalysisProductChannelCount.

Definition catalysisBundleHolds (b : ccv_channel_bundle) (idx : nat) : bool :=
  ccv_channel_slot_is_present (b idx).

Definition catalysisBundleIsConcurrentProduct (b : ccv_channel_bundle) : bool :=
  Nat.leb 2 (catalysisBundlePresentCount b).

(* Pt Z=78 interact restriction + G-min + class 14 catalysis concurrent witness. *)
Definition catalysisPt78Witness : ccv_channel_bundle :=
  catalysisBundleWithPresent
    (catalysisBundleWithPresent
      (catalysisBundleWithPresent catalysisBundleAllUnwired
        ccv_channel_interact_restriction)
      ccv_channel_tst_prior_art)
    ccv_channel_class9_catalysis.

Definition catalysisEmptyWitness : ccv_channel_bundle :=
  catalysisBundleAllUnwired.

Definition catalysisSinglePresent : ccv_channel_bundle :=
  catalysisBundleWithPresent catalysisBundleAllUnwired
    ccv_channel_interact_restriction.

Lemma interact_restriction_channel_present :
  catalysisBundleHolds catalysisPt78Witness
    ccv_channel_interact_restriction = true.
Proof. reflexivity. Qed.

Lemma tst_prior_art_channel_present :
  catalysisBundleHolds catalysisPt78Witness
    ccv_channel_tst_prior_art = true.
Proof. reflexivity. Qed.

Lemma class9_catalysis_channel_present :
  catalysisBundleHolds catalysisPt78Witness
    ccv_channel_class9_catalysis = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  catalysisBundlePresentCount catalysisPt78Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  catalysisBundleIsConcurrentProduct catalysisPt78Witness = true.
Proof.
  unfold catalysisBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  catalysisBundlePresentCount catalysisEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  catalysisBundleIsConcurrentProduct catalysisEmptyWitness = false.
Proof.
  unfold catalysisBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  catalysisBundlePresentCount catalysisSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  catalysisBundleIsConcurrentProduct catalysisSinglePresent = false.
Proof.
  unfold catalysisBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ccv_xor_posture : Type :=
  | ccv_xor_exclusive
  | ccv_xor_concurrent_product.

Definition prcXorClassifierMarker : string := "chem_l0_catalysis_xor_classifier_v1".
Definition prcConcurrentProductMarker : string := "chem_int_catalysis_product_v1".

Lemma ccv_xor_marker_ne_concurrent_product_marker :
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition prcXorClassifierIncompatible (claim_xor : bool)
  (b : ccv_channel_bundle) : bool :=
  claim_xor && catalysisBundleIsConcurrentProduct b.

Lemma ccv_xor_refuse_on_pt78_witness :
  prcXorClassifierIncompatible true catalysisPt78Witness = true.
Proof.
  unfold prcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma ccv_xor_ok_on_concurrent_product_claim :
  prcXorClassifierIncompatible false catalysisPt78Witness = false.
Proof. reflexivity. Qed.

Definition prcProductNotXor : bool :=
  catalysisBundleIsConcurrentProduct catalysisPt78Witness &&
  prcXorClassifierIncompatible true catalysisPt78Witness.

Lemma ccv_product_not_xor_true : prcProductNotXor = true.
Proof.
  unfold prcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  prcProductNotXor = true /\
  Nat.leb 2 (catalysisBundlePresentCount
    catalysisPt78Witness) = true /\
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof.
  split.
  - apply ccv_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply ccv_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive ccv_bar_presence : Type :=
  | ccv_bar_absent
  | ccv_bar_present.

Record ccv_claim_bar : Type := {
  ccv_bar_presence_field : ccv_bar_presence;
  ccv_bar_defect_total : nat
}.

Definition catalysisClaimBarAbsent : ccv_claim_bar :=
  {| ccv_bar_presence_field := ccv_bar_absent;
     ccv_bar_defect_total := 0 |}.

Definition catalysisClaimBarZeroDefect : ccv_claim_bar :=
  {| ccv_bar_presence_field := ccv_bar_present;
     ccv_bar_defect_total := 0 |}.

Definition ccv_claim_bar_zero_defect (b : ccv_claim_bar) : bool :=
  match ccv_bar_presence_field b with
  | ccv_bar_absent => false
  | ccv_bar_present => Nat.eqb (ccv_bar_defect_total b) 0
  end.

Lemma ccv_claim_bar_zero_defect_true :
  ccv_claim_bar_zero_defect catalysisClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma ccv_claim_bar_absent_not_zero_defect :
  ccv_claim_bar_zero_defect catalysisClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive ccv_conservation_verdict : Type :=
  | ccv_verdict_unwired_ok
  | ccv_verdict_named_ok
  | ccv_verdict_design_ok
  | ccv_verdict_trivial_refuse
  | ccv_verdict_xor_refuse
  | ccv_verdict_green_invent_refuse
  | ccv_verdict_proved_without_bar_refuse
  | ccv_verdict_production_wired_refuse
  | ccv_verdict_parallel_catalysis_axiom_refuse
  | ccv_verdict_species_id_smuggle_refuse
  | ccv_verdict_extra_element_id_refuse
  | ccv_verdict_extra_catalysis_force_refuse
  | ccv_verdict_tp_float_pin_refuse.

Definition ccv_conservation_verdict_ok (v : ccv_conservation_verdict) : bool :=
  match v with
  | ccv_verdict_unwired_ok => true
  | ccv_verdict_named_ok => true
  | ccv_verdict_design_ok => true
  | _ => false
  end.

Definition catalysisBundleNontrivial (b : ccv_channel_bundle) : bool :=
  Nat.ltb 0 (catalysisBundlePresentCount b).

Definition evaluate_catalysis_bundle
  (m : CatalysisConservationModality)
  (b : ccv_channel_bundle)
  (bar : ccv_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : ccv_conservation_verdict :=
  if claim_physics_green
  then ccv_verdict_green_invent_refuse
  else if claim_proved
       then ccv_verdict_proved_without_bar_refuse
       else if negb (catalysisBundleNontrivial b)
            then ccv_verdict_trivial_refuse
            else if prcXorClassifierIncompatible claim_xor_classifier b
                 then ccv_verdict_xor_refuse
                 else
                   match m with
                   | catalysis_conservation_unwired =>
                       if catalysisBundleIsConcurrentProduct b
                       then ccv_verdict_named_ok
                       else ccv_verdict_design_ok
                   | catalysis_conservation_assumed
                   | catalysis_conservation_surrogate =>
                       ccv_verdict_design_ok
                   | catalysis_conservation_proved =>
                       ccv_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_catalysis_conservation_close
  (m : CatalysisConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : ccv_conservation_verdict :=
  if claim_physics_green
  then ccv_verdict_green_invent_refuse
  else if claim_production_wired
  then ccv_verdict_production_wired_refuse
  else
    match m with
    | catalysis_conservation_unwired => ccv_verdict_unwired_ok
    | catalysis_conservation_assumed
    | catalysis_conservation_proved
    | catalysis_conservation_surrogate => ccv_verdict_named_ok
    end.

Definition catalysis_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_catalysis_conservation_close
          catalysis_conservation_proved claim_physics_green claim_production_wired with
  | ccv_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive ccv_conservation_law : Type :=
  | ccv_law_conserved
  | ccv_law_named_ok
  | ccv_law_trivial_refuse
  | ccv_law_green_invent_refuse.

Definition ccv_conservation_law_count : nat := 4.

Lemma ccv_conservation_law_count_is_four :
  ccv_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive ccv_conservation_law_witness : Type :=
  | ccv_law_witness_open
  | ccv_law_witness_proved.

Definition evaluate_ccv_conservation_law_witness
  (law : ccv_conservation_law)
  (m : CatalysisConservationModality)
  : ccv_conservation_law_witness :=
  match m with
  | catalysis_conservation_unwired
  | catalysis_conservation_assumed
  | catalysis_conservation_surrogate => ccv_law_witness_open
  | catalysis_conservation_proved => ccv_law_witness_proved
  end.

Lemma all_ccv_conservation_laws_open_at_unwired :
  evaluate_ccv_conservation_law_witness ccv_law_conserved
    catalysis_conservation_unwired = ccv_law_witness_open /\
  evaluate_ccv_conservation_law_witness ccv_law_named_ok
    catalysis_conservation_unwired = ccv_law_witness_open /\
  evaluate_ccv_conservation_law_witness ccv_law_trivial_refuse
    catalysis_conservation_unwired = ccv_law_witness_open /\
  evaluate_ccv_conservation_law_witness ccv_law_green_invent_refuse
    catalysis_conservation_unwired = ccv_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition catalysisConservationProved : bool := false.

Lemma catalysis_conservation_proved_false :
  catalysisConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_catalysis_conservation_close
    catalysis_conservation_unwired false false =
  ccv_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_catalysis_conservation_close
    catalysis_conservation_unwired false false =
  ccv_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_unwired false false) =
  true.
Proof.
  unfold ccv_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt78_witness_named_ok :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false false =
  ccv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_catalysis_conservation :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false false =
  ccv_verdict_named_ok /\
  catalysisBundleIsConcurrentProduct catalysisPt78Witness = true /\
  platinum_atomic_number_z = 78 /\
  pattern_class_catalysis_idx = 14.
Proof.
  repeat split; reflexivity.
Qed.

Lemma ccv_named_close_ok :
  evaluate_catalysis_conservation_close
    catalysis_conservation_proved false false =
  ccv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_catalysis_conservation_close :
  evaluate_catalysis_conservation_close
    catalysis_conservation_proved false false =
  ccv_verdict_named_ok /\
  catalysis_conservation_authorized false false = true.
Proof.
  split.
  - apply ccv_named_close_ok.
  - unfold catalysis_conservation_authorized.
    rewrite ccv_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — catalysis refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisEmptyWitness
    catalysisClaimBarAbsent false false false =
  ccv_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisEmptyWitness
    catalysisClaimBarAbsent false false false =
  ccv_verdict_trivial_refuse /\
  ccv_conservation_verdict_ok
    (evaluate_catalysis_bundle
       catalysis_conservation_unwired
       catalysisEmptyWitness
       catalysisClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold ccv_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent true false false =
  ccv_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent true false false =
  ccv_verdict_xor_refuse /\
  ccv_conservation_verdict_ok
    (evaluate_catalysis_bundle
       catalysis_conservation_unwired
       catalysisPt78Witness
       catalysisClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold ccv_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_catalysis_conservation_close
    catalysis_conservation_unwired true false =
  ccv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_unwired true false) =
  false.
Proof.
  unfold ccv_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ccv_bundle_refuse :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false true false =
  ccv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — catalysis refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false true =
  ccv_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false true =
  ccv_verdict_proved_without_bar_refuse /\
  ccv_conservation_verdict_ok
    (evaluate_catalysis_bundle
       catalysis_conservation_unwired
       catalysisPt78Witness
       catalysisClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold ccv_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — catalysis lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_catalysis_conservation_close
    catalysis_conservation_proved false true =
  ccv_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_proved false true) =
  false.
Proof.
  unfold ccv_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel catalysis axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition catalysisConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/catalysis.rs".

Definition parallelCatalysisAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_catalysis_axiom_refuse :
  catalysisConservationAuthority <>
  parallelCatalysisAxiomTag /\
  catalysisConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply catalysis_conservation_proved_false.
Qed.

Theorem parallel_catalysis_axiom_not_minted :
  catalysisConservationAuthority =
  "umst/umst-chem/src/l0_tables/catalysis.rs" /\
  catalysisConservationProved = false /\
  catalysisConservationAuthority <> parallelCatalysisAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "tst_prior_art_not_named_object".

Definition catalysisConservationFraming : string :=
  "second_law_conservation_catalysis_interact_restriction_one_axiom".

Lemma species_id_smuggle_refuse :
  catalysisConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_catalysis_idx = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem interact_restriction_not_species_id_smuggle :
  catalysisConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_catalysis_idx = 14 /\
  catalysisConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — catalysis ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "catalyst_consumed_in_net_reaction".

Lemma extra_element_id_refuse :
  catalysisConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  catalysisConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — catalysis ≠ extra catalysis force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraCatalysisForceFraming : string :=
  "extra_catalysis_force_axiom_minted_as_26th_law".

Definition catalysisBarrierAuthority : string :=
  "umst/umst-chem/src/catalysis_barrier.rs".

Lemma extra_catalysis_force_refuse :
  catalysisConservationFraming <>
  extraCatalysisForceFraming /\
  catalysisBarrierAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem catalysis_not_extra_catalysis_force :
  catalysisConservationFraming <>
  extraCatalysisForceFraming /\
  catalysisBarrierAuthority =
  "umst/umst-chem/src/catalysis_barrier.rs" /\
  catalysisConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_catalysis_scaffold".

Lemma tp_float_pin_refuse :
  catalysisConservationFraming <>
  tpFloatPinFraming /\
  interact_restriction_channel_tag = "interact_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  catalysisConservationFraming <>
  tpFloatPinFraming /\
  tst_prior_art_channel_tag = "tst_prior_art" /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition ccv_conservation_coherence_scaffold : bool :=
  ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_proved false false) &&
  negb (ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_unwired true false)) &&
  negb (ccv_conservation_verdict_ok
    (evaluate_catalysis_conservation_close
       catalysis_conservation_proved false true)).

Lemma ccv_conservation_coherence_scaffold_true :
  ccv_conservation_coherence_scaffold = true.
Proof.
  unfold ccv_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem ccv_conservation_coherence_scaffold_theorem :
  evaluate_catalysis_conservation_close
    catalysis_conservation_proved false false =
    ccv_verdict_named_ok /\
  evaluate_catalysis_conservation_close
    catalysis_conservation_unwired true false =
    ccv_verdict_green_invent_refuse /\
  evaluate_catalysis_conservation_close
    catalysis_conservation_proved false true =
    ccv_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition ccv_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition ccv_conservation_knowing_fiber_ok : bool :=
  ccv_conservation_fiber_ok fiber_quantum_knowing.

Definition ccv_conservation_meso_acting_ok : bool :=
  ccv_conservation_fiber_ok fiber_meso_acting.

Lemma ccv_conservation_knowing_fiber_ok_true :
  ccv_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma ccv_conservation_meso_acting_not_ok :
  ccv_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem ccv_conservation_routes_knowing_not_meso :
  ccv_conservation_knowing_fiber_ok = true /\
  ccv_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply ccv_conservation_knowing_fiber_ok_true.
  - apply ccv_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  ccv_conservation_knowing_fiber_ok &&
  negb ccv_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, ccv_conservation_knowing_fiber_ok,
    ccv_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem catalysis_conservation_fixture_scaffold :
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false false =
    ccv_verdict_named_ok /\
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisEmptyWitness
    catalysisClaimBarAbsent false false false =
    ccv_verdict_trivial_refuse /\
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent true false false =
    ccv_verdict_xor_refuse /\
  evaluate_catalysis_bundle
    catalysis_conservation_unwired
    catalysisPt78Witness
    catalysisClaimBarAbsent false false true =
    ccv_verdict_proved_without_bar_refuse /\
  evaluate_catalysis_conservation_close
    catalysis_conservation_unwired false false =
    ccv_verdict_unwired_ok /\
  ccv_conservation_knowing_fiber_ok = true /\
  ccv_conservation_meso_acting_ok = false /\
  catalysisConservationProved = false /\
  prcProductNotXor = true /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — catalysis) *)
(* ------------------------------------------------------------------ *)

Definition chemL0CatalysisAuthority : string :=
  "umst/umst-chem/src/catalysis.rs".

Definition chemL0CatalysisTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/catalysis.rs".

Definition interactPartialityAuthority : string :=
  "umst/umst-chem/src/interact_partiality.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeCatalysisCellId : string := "CHEM-L0-EDGE-CATALYSIS".

Definition catalysisConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-CATALYSIS-CONSERVATION".

Definition catalysisConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CATALYSIS-CONSERVATION CatalysisConservationModality Unwired Assumed Proved Surrogate four-step lattice catalysisConservationProved false evaluateCatalysisBundle evaluateCatalysisConservation named class 14 catalysis Pt Z=78 interact restriction second law TST prior art concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel catalysis axiom refuse species id smuggle refuse extra element id Z=119 refuse extra catalysis force CAT-03 refuse catalysis ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma catalysis_conservation_cell_id :
  catalysisConservationCellId =
  "CHEM-FORMAL-Q-COQ-CATALYSIS-CONSERVATION".
Proof. reflexivity. Qed.

Lemma catalysis_conservation_cites_l0_table :
  chemL0CatalysisTableAuthority <> "".
Proof. discriminate. Qed.

Lemma catalysis_conservation_authority_path :
  catalysisConservationAuthority =
  "umst/umst-chem/src/l0_tables/catalysis.rs".
Proof. reflexivity. Qed.

Lemma catalysis_conservation_cites_l0_ore02 :
  chemL0CatalysisAuthority <> "".
Proof. discriminate. Qed.

Lemma catalysis_conservation_cites_marker :
  prcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma catalysis_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma catalysis_conservation_cites_ore02_cell :
  chemL0EdgeCatalysisCellId = "CHEM-L0-EDGE-CATALYSIS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma catalysis_not_26th_axiom :
  catalysisConservationFraming <> parallelCatalysisAxiomTag.
Proof. discriminate. Qed.

Lemma catalysis_second_law_conservation_framing :
  catalysisConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition tstPriorArtFraming : string :=
  "transition_state_theory_prior_art_not_named_object".

Definition interactRestrictionNamedObject : string :=
  "interact_restriction_on_catalysis_morphism".

Lemma tst_prior_art_not_named_object :
  interactRestrictionNamedObject <>
  tstPriorArtFraming /\
  tst_prior_art_channel_tag = "tst_prior_art".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem interact_restriction_is_named_object_not_tst :
  interactRestrictionNamedObject <>
  tstPriorArtFraming /\
  interact_restriction_channel_tag = "interact_restriction" /\
  catalysisConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not catalysis axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition interactRestrictionFraming : string :=
  "interact_restriction_not_extra_force".

Lemma interact_restriction_not_extra_force_refuse :
  interactRestrictionFraming <>
  extraCatalysisForceFraming /\
  interact_restriction_channel_tag = "interact_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem catalysis_interact_restriction_not_extra_force :
  interactRestrictionFraming <>
  extraCatalysisForceFraming /\
  catalysisBarrierAuthority =
  "umst/umst-chem/src/catalysis_barrier.rs" /\
  catalysisConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma catalysis_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma catalysis_conservation_modality_unwired :
  catalysisConservationModalityCurrent =
  catalysis_conservation_unwired.
Proof. reflexivity. Qed.

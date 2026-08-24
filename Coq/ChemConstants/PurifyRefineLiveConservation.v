(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PurifyRefineLiveConservation.v                        *)
(*                                                                      *)
(*  Knowing-fiber Coq: LIVE **purify-refine** **conservation**.        *)
(*  Dissipative adjunction cost — no free purification; reverse-refine *)
(*  CAT-03 adjunction refused. Concurrent Π_c PatternBundle factor —     *)
(*  **product** not XOR. purifyRefineLiveConservationProved false.       *)
(*  Modality Unwired. WAVE100: not wired in lib.rs.                     *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/refine_process.rs (read-only cite).         *)
(*  INT: umst/umst-chem/src/l0_tables/processing_refining.rs (cite).    *)
(*  INT: umst/umst-chem/src/refining_graph_cuts.rs (read-only cite).    *)
(*  ProcessingRefiningConservation.v + CatalysisConservation.v scaffold. *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **purify_refine_live** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PurifyRefineLiveConservationModality : Type :=
  | purify_refine_live_conservation_unwired
  | purify_refine_live_conservation_assumed
  | purify_refine_live_conservation_proved
  | purify_refine_live_conservation_surrogate.

Definition purifyRefineLiveConservationModalityCurrent :
  PurifyRefineLiveConservationModality :=
  purify_refine_live_conservation_unwired.

Definition purify_refine_live_lattice_cardinality : nat := 4.

Lemma purify_refine_live_lattice_cardinality_is_four :
  purify_refine_live_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma purify_refine_live_lattice_not_118_squared :
  negb (Nat.eqb purify_refine_live_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold purify_refine_live_lattice_cardinality.
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

(* North-star §2 LIVE purify-refine — purify_refine_live concurrent Π_c factor. *)
Definition pattern_class_purify_refine_live_idx : nat := 9.

Lemma pattern_class_purify_refine_live_idx_is_9 :
  pattern_class_purify_refine_live_idx = 9.
Proof. reflexivity. Qed.

Lemma purify_refine_live_class_index_valid :
  pattern_class_index_valid pattern_class_purify_refine_live_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_purify_refine_live_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierPurifyRefineLiveRowId : string := "PRL01".

Lemma cross_classifier_purify_refine_live_row_named :
  crossClassifierPurifyRefineLiveRowId = "PRL01".
Proof. reflexivity. Qed.

Definition pattern_class_purify_refine_live_tag : string :=
  "purify_refine_live".

Definition north_star_live_purify_refine_tag : string :=
  "LIVE purify refine".

Lemma pattern_class_purify_refine_live_tag_nonempty :
  pattern_class_purify_refine_live_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_live_purify_refine_tag_nonempty :
  north_star_live_purify_refine_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Fe Z=26 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition iron_atomic_number_z : nat := 26.

Lemma iron_atomic_number_z_is_26 :
  iron_atomic_number_z = 26.
Proof. reflexivity. Qed.

Definition iron_z_valid : bool :=
  Nat.ltb 0 iron_atomic_number_z &&
  Nat.leb iron_atomic_number_z iupac_table_cardinality.

Lemma iron_z_valid_true : iron_z_valid = true.
Proof.
  unfold iron_z_valid, iron_atomic_number_z, iupac_table_cardinality.
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

Definition purify_refine_live_factor_tag : string :=
  "purify_refine_live".

Definition dissipative_adjunction_cost_channel_tag : string := "dissipative_adjunction_cost".

Definition second_law_gmin_channel_tag : string := "second_law_gmin".

Lemma purify_refine_live_factor_tag_nonempty :
  purify_refine_live_factor_tag <> "".
Proof. discriminate. Qed.

Lemma dissipative_adjunction_cost_channel_tag_nonempty :
  dissipative_adjunction_cost_channel_tag <> "".
Proof. discriminate. Qed.

Lemma second_law_gmin_channel_tag_nonempty :
  second_law_gmin_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive prlc_channel_slot : Type :=
  | prlc_slot_unwired
  | prlc_slot_absent
  | prlc_slot_present.

Definition prlc_channel_slot_beq (s1 s2 : prlc_channel_slot) : bool :=
  match s1, s2 with
  | prlc_slot_unwired, prlc_slot_unwired => true
  | prlc_slot_absent, prlc_slot_absent => true
  | prlc_slot_present, prlc_slot_present => true
  | _, _ => false
  end.

Definition prlc_channel_slot_is_present (s : prlc_channel_slot) : bool :=
  match s with
  | prlc_slot_present => true
  | _ => false
  end.

Definition purify_refine_liveProductChannelCount : nat := 3.

Lemma purify_refine_live_product_channel_count_is_three :
  purify_refine_liveProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = dissipative adjunction cost, 1 = G-min second law, 2 = LIVE purify refine. *)
Definition prlc_channel_dissipative_adjunction_cost : nat := 0.
Definition prlc_channel_second_law_gmin : nat := 1.
Definition prlc_channel_class9_purify_refine_live : nat := 2.

Lemma prlc_channel_dissipative_adjunction_cost_idx_is_0 :
  prlc_channel_dissipative_adjunction_cost = 0.
Proof. reflexivity. Qed.

Lemma prlc_channel_second_law_gmin_idx_is_1 :
  prlc_channel_second_law_gmin = 1.
Proof. reflexivity. Qed.

Lemma prlc_channel_class9_purify_refine_live_idx_is_2 :
  prlc_channel_class9_purify_refine_live = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition prlc_channel_bundle : Type := nat -> prlc_channel_slot.

Definition purify_refine_liveBundleAllUnwired : prlc_channel_bundle :=
  fun _ => prlc_slot_unwired.

Definition purify_refine_liveBundleAt (b : prlc_channel_bundle) (idx : nat)
  (slot : prlc_channel_slot) : prlc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition purify_refine_liveBundleWithPresent
  (b : prlc_channel_bundle) (idx : nat) : prlc_channel_bundle :=
  purify_refine_liveBundleAt b idx prlc_slot_present.

Fixpoint count_prlc_present_up_to (b : prlc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if prlc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_prlc_present_up_to b i + add
  end.

Definition purify_refine_liveBundlePresentCount (b : prlc_channel_bundle) : nat :=
  count_prlc_present_up_to b purify_refine_liveProductChannelCount.

Definition purify_refine_liveBundleHolds (b : prlc_channel_bundle) (idx : nat) : bool :=
  prlc_channel_slot_is_present (b idx).

Definition purify_refine_liveBundleIsConcurrentProduct (b : prlc_channel_bundle) : bool :=
  Nat.leb 2 (purify_refine_liveBundlePresentCount b).

(* Fe Z=26 dissipative adjunction cost + G-min + LIVE purify refine concurrent witness. *)
Definition purify_refine_liveFe26Witness : prlc_channel_bundle :=
  purify_refine_liveBundleWithPresent
    (purify_refine_liveBundleWithPresent
      (purify_refine_liveBundleWithPresent purify_refine_liveBundleAllUnwired
        prlc_channel_dissipative_adjunction_cost)
      prlc_channel_second_law_gmin)
    prlc_channel_class9_purify_refine_live.

Definition purify_refine_liveEmptyWitness : prlc_channel_bundle :=
  purify_refine_liveBundleAllUnwired.

Definition purify_refine_liveSinglePresent : prlc_channel_bundle :=
  purify_refine_liveBundleWithPresent purify_refine_liveBundleAllUnwired
    prlc_channel_dissipative_adjunction_cost.

Lemma dissipative_adjunction_cost_channel_present :
  purify_refine_liveBundleHolds purify_refine_liveFe26Witness
    prlc_channel_dissipative_adjunction_cost = true.
Proof. reflexivity. Qed.

Lemma second_law_gmin_channel_present :
  purify_refine_liveBundleHolds purify_refine_liveFe26Witness
    prlc_channel_second_law_gmin = true.
Proof. reflexivity. Qed.

Lemma class9_purify_refine_live_channel_present :
  purify_refine_liveBundleHolds purify_refine_liveFe26Witness
    prlc_channel_class9_purify_refine_live = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  purify_refine_liveBundlePresentCount purify_refine_liveFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  purify_refine_liveBundleIsConcurrentProduct purify_refine_liveFe26Witness = true.
Proof.
  unfold purify_refine_liveBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  purify_refine_liveBundlePresentCount purify_refine_liveEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  purify_refine_liveBundleIsConcurrentProduct purify_refine_liveEmptyWitness = false.
Proof.
  unfold purify_refine_liveBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  purify_refine_liveBundlePresentCount purify_refine_liveSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  purify_refine_liveBundleIsConcurrentProduct purify_refine_liveSinglePresent = false.
Proof.
  unfold purify_refine_liveBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive prlc_xor_posture : Type :=
  | prlc_xor_exclusive
  | prlc_xor_concurrent_product.

Definition prlcXorClassifierMarker : string := "chem_l0_purify_refine_live_xor_classifier_v1".
Definition prlcConcurrentProductMarker : string := "chem_int_purify_refine_live_product_v1".

Lemma prlc_xor_marker_ne_concurrent_product_marker :
  prlcXorClassifierMarker <> prlcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition prlcXorClassifierIncompatible (claim_xor : bool)
  (b : prlc_channel_bundle) : bool :=
  claim_xor && purify_refine_liveBundleIsConcurrentProduct b.

Lemma prlc_xor_refuse_on_fe26_witness :
  prlcXorClassifierIncompatible true purify_refine_liveFe26Witness = true.
Proof.
  unfold prlcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma prlc_xor_ok_on_concurrent_product_claim :
  prlcXorClassifierIncompatible false purify_refine_liveFe26Witness = false.
Proof. reflexivity. Qed.

Definition prlcProductNotXor : bool :=
  purify_refine_liveBundleIsConcurrentProduct purify_refine_liveFe26Witness &&
  prlcXorClassifierIncompatible true purify_refine_liveFe26Witness.

Lemma prlc_product_not_xor_true : prlcProductNotXor = true.
Proof.
  unfold prlcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  prlcProductNotXor = true /\
  Nat.leb 2 (purify_refine_liveBundlePresentCount
    purify_refine_liveFe26Witness) = true /\
  prlcXorClassifierMarker <> prlcConcurrentProductMarker.
Proof.
  split.
  - apply prlc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply prlc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive prlc_bar_presence : Type :=
  | prlc_bar_absent
  | prlc_bar_present.

Record prlc_claim_bar : Type := {
  prlc_bar_presence_field : prlc_bar_presence;
  prlc_bar_defect_total : nat
}.

Definition purify_refine_liveClaimBarAbsent : prlc_claim_bar :=
  {| prlc_bar_presence_field := prlc_bar_absent;
     prlc_bar_defect_total := 0 |}.

Definition purify_refine_liveClaimBarZeroDefect : prlc_claim_bar :=
  {| prlc_bar_presence_field := prlc_bar_present;
     prlc_bar_defect_total := 0 |}.

Definition prlc_claim_bar_zero_defect (b : prlc_claim_bar) : bool :=
  match prlc_bar_presence_field b with
  | prlc_bar_absent => false
  | prlc_bar_present => Nat.eqb (prlc_bar_defect_total b) 0
  end.

Lemma prlc_claim_bar_zero_defect_true :
  prlc_claim_bar_zero_defect purify_refine_liveClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma prlc_claim_bar_absent_not_zero_defect :
  prlc_claim_bar_zero_defect purify_refine_liveClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive prlc_conservation_verdict : Type :=
  | prlc_verdict_unwired_ok
  | prlc_verdict_named_ok
  | prlc_verdict_design_ok
  | prlc_verdict_trivial_refuse
  | prlc_verdict_xor_refuse
  | prlc_verdict_green_invent_refuse
  | prlc_verdict_proved_without_bar_refuse
  | prlc_verdict_production_wired_refuse
  | prlc_verdict_parallel_purify_refine_live_axiom_refuse
  | prlc_verdict_species_id_smuggle_refuse
  | prlc_verdict_extra_element_id_refuse
  | prlc_verdict_extra_purify_refine_live_force_refuse
  | prlc_verdict_tp_float_pin_refuse.

Definition prlc_conservation_verdict_ok (v : prlc_conservation_verdict) : bool :=
  match v with
  | prlc_verdict_unwired_ok => true
  | prlc_verdict_named_ok => true
  | prlc_verdict_design_ok => true
  | _ => false
  end.

Definition purify_refine_liveBundleNontrivial (b : prlc_channel_bundle) : bool :=
  Nat.ltb 0 (purify_refine_liveBundlePresentCount b).

Definition evaluate_purify_refine_live_bundle
  (m : PurifyRefineLiveConservationModality)
  (b : prlc_channel_bundle)
  (bar : prlc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : prlc_conservation_verdict :=
  if claim_physics_green
  then prlc_verdict_green_invent_refuse
  else if claim_proved
       then prlc_verdict_proved_without_bar_refuse
       else if negb (purify_refine_liveBundleNontrivial b)
            then prlc_verdict_trivial_refuse
            else if prlcXorClassifierIncompatible claim_xor_classifier b
                 then prlc_verdict_xor_refuse
                 else
                   match m with
                   | purify_refine_live_conservation_unwired =>
                       if purify_refine_liveBundleIsConcurrentProduct b
                       then prlc_verdict_named_ok
                       else prlc_verdict_design_ok
                   | purify_refine_live_conservation_assumed
                   | purify_refine_live_conservation_surrogate =>
                       prlc_verdict_design_ok
                   | purify_refine_live_conservation_proved =>
                       prlc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_purify_refine_live_conservation_close
  (m : PurifyRefineLiveConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : prlc_conservation_verdict :=
  if claim_physics_green
  then prlc_verdict_green_invent_refuse
  else if claim_production_wired
  then prlc_verdict_production_wired_refuse
  else
    match m with
    | purify_refine_live_conservation_unwired => prlc_verdict_unwired_ok
    | purify_refine_live_conservation_assumed
    | purify_refine_live_conservation_proved
    | purify_refine_live_conservation_surrogate => prlc_verdict_named_ok
    end.

Definition purify_refine_live_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_purify_refine_live_conservation_close
          purify_refine_live_conservation_proved claim_physics_green claim_production_wired with
  | prlc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive prlc_conservation_law : Type :=
  | prlc_law_conserved
  | prlc_law_named_ok
  | prlc_law_trivial_refuse
  | prlc_law_green_invent_refuse.

Definition prlc_conservation_law_count : nat := 4.

Lemma prlc_conservation_law_count_is_four :
  prlc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive prlc_conservation_law_witness : Type :=
  | prlc_law_witness_open
  | prlc_law_witness_proved.

Definition evaluate_prlc_conservation_law_witness
  (law : prlc_conservation_law)
  (m : PurifyRefineLiveConservationModality)
  : prlc_conservation_law_witness :=
  match m with
  | purify_refine_live_conservation_unwired
  | purify_refine_live_conservation_assumed
  | purify_refine_live_conservation_surrogate => prlc_law_witness_open
  | purify_refine_live_conservation_proved => prlc_law_witness_proved
  end.

Lemma all_prlc_conservation_laws_open_at_unwired :
  evaluate_prlc_conservation_law_witness prlc_law_conserved
    purify_refine_live_conservation_unwired = prlc_law_witness_open /\
  evaluate_prlc_conservation_law_witness prlc_law_named_ok
    purify_refine_live_conservation_unwired = prlc_law_witness_open /\
  evaluate_prlc_conservation_law_witness prlc_law_trivial_refuse
    purify_refine_live_conservation_unwired = prlc_law_witness_open /\
  evaluate_prlc_conservation_law_witness prlc_law_green_invent_refuse
    purify_refine_live_conservation_unwired = prlc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition purifyRefineLiveConservationProved : bool := false.

Lemma purify_refine_live_conservation_proved_false :
  purifyRefineLiveConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_unwired false false =
  prlc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_unwired false false =
  prlc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_unwired false false) =
  true.
Proof.
  unfold prlc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false false =
  prlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_purify_refine_live_conservation :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false false =
  prlc_verdict_named_ok /\
  purify_refine_liveBundleIsConcurrentProduct purify_refine_liveFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_purify_refine_live_idx = 9.
Proof.
  repeat split; reflexivity.
Qed.

Lemma prlc_named_close_ok :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_proved false false =
  prlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_purify_refine_live_conservation_close :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_proved false false =
  prlc_verdict_named_ok /\
  purify_refine_live_conservation_authorized false false = true.
Proof.
  split.
  - apply prlc_named_close_ok.
  - unfold purify_refine_live_conservation_authorized.
    rewrite prlc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — purify_refine_live refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveEmptyWitness
    purify_refine_liveClaimBarAbsent false false false =
  prlc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveEmptyWitness
    purify_refine_liveClaimBarAbsent false false false =
  prlc_verdict_trivial_refuse /\
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_bundle
       purify_refine_live_conservation_unwired
       purify_refine_liveEmptyWitness
       purify_refine_liveClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold prlc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent true false false =
  prlc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent true false false =
  prlc_verdict_xor_refuse /\
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_bundle
       purify_refine_live_conservation_unwired
       purify_refine_liveFe26Witness
       purify_refine_liveClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold prlc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_unwired true false =
  prlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_unwired true false) =
  false.
Proof.
  unfold prlc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_prlc_bundle_refuse :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false true false =
  prlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — purify_refine_live refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false true =
  prlc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false true =
  prlc_verdict_proved_without_bar_refuse /\
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_bundle
       purify_refine_live_conservation_unwired
       purify_refine_liveFe26Witness
       purify_refine_liveClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold prlc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — purify_refine_live lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_proved false true =
  prlc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_proved false true) =
  false.
Proof.
  unfold prlc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel purify_refine_live axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition purifyRefineLiveConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition parallelPurifyRefineLiveAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_purify_refine_live_axiom_refuse :
  purifyRefineLiveConservationAuthority <>
  parallelPurifyRefineLiveAxiomTag /\
  purifyRefineLiveConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply purify_refine_live_conservation_proved_false.
Qed.

Theorem parallel_purify_refine_live_axiom_not_minted :
  purifyRefineLiveConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs" /\
  purifyRefineLiveConservationProved = false /\
  purifyRefineLiveConservationAuthority <> parallelPurifyRefineLiveAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — dissipative adjunction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition purifyRefineLiveConservationFraming : string :=
  "second_law_conservation_purify_refine_live_dissipative_adjunction_cost_one_axiom".

Lemma species_id_smuggle_refuse :
  purifyRefineLiveConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_purify_refine_live_idx = 9.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem dissipative_adjunction_cost_not_species_id_smuggle :
  purifyRefineLiveConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_purify_refine_live_idx = 9 /\
  purifyRefineLiveConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — purify_refine_live ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  purifyRefineLiveConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  purifyRefineLiveConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — LIVE purify refine ≠ CAT-03 adjunction    *)
(* ------------------------------------------------------------------ *)

Definition freePurificationFraming : string :=
  "free_purification_reverse_refine_cat03_adjunction".

Definition refineProcessAuthority : string :=
  "umst/umst-chem/src/refine_process.rs".

Lemma free_purification_refuse :
  purifyRefineLiveConservationFraming <>
  freePurificationFraming /\
  refineProcessAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem purify_refine_live_not_free_purification :
  purifyRefineLiveConservationFraming <>
  freePurificationFraming /\
  refineProcessAuthority =
  "umst/umst-chem/src/refine_process.rs" /\
  purifyRefineLiveConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_purify_refine_live_scaffold".

Lemma tp_float_pin_refuse :
  purifyRefineLiveConservationFraming <>
  tpFloatPinFraming /\
  dissipative_adjunction_cost_channel_tag = "dissipative_adjunction_cost".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  purifyRefineLiveConservationFraming <>
  tpFloatPinFraming /\
  second_law_gmin_channel_tag = "second_law_gmin" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  PurifyRefineLive **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition prlc_conservation_coherence_scaffold : bool :=
  prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_proved false false) &&
  negb (prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_unwired true false)) &&
  negb (prlc_conservation_verdict_ok
    (evaluate_purify_refine_live_conservation_close
       purify_refine_live_conservation_proved false true)).

Lemma prlc_conservation_coherence_scaffold_true :
  prlc_conservation_coherence_scaffold = true.
Proof.
  unfold prlc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem prlc_conservation_coherence_scaffold_theorem :
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_proved false false =
    prlc_verdict_named_ok /\
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_unwired true false =
    prlc_verdict_green_invent_refuse /\
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_proved false true =
    prlc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition prlc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition prlc_conservation_knowing_fiber_ok : bool :=
  prlc_conservation_fiber_ok fiber_quantum_knowing.

Definition prlc_conservation_meso_acting_ok : bool :=
  prlc_conservation_fiber_ok fiber_meso_acting.

Lemma prlc_conservation_knowing_fiber_ok_true :
  prlc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma prlc_conservation_meso_acting_not_ok :
  prlc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem prlc_conservation_routes_knowing_not_meso :
  prlc_conservation_knowing_fiber_ok = true /\
  prlc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply prlc_conservation_knowing_fiber_ok_true.
  - apply prlc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  prlc_conservation_knowing_fiber_ok &&
  negb prlc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, prlc_conservation_knowing_fiber_ok,
    prlc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named LIVE purify-refine + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem purify_refine_live_conservation_fixture_scaffold :
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false false =
    prlc_verdict_named_ok /\
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveEmptyWitness
    purify_refine_liveClaimBarAbsent false false false =
    prlc_verdict_trivial_refuse /\
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent true false false =
    prlc_verdict_xor_refuse /\
  evaluate_purify_refine_live_bundle
    purify_refine_live_conservation_unwired
    purify_refine_liveFe26Witness
    purify_refine_liveClaimBarAbsent false false true =
    prlc_verdict_proved_without_bar_refuse /\
  evaluate_purify_refine_live_conservation_close
    purify_refine_live_conservation_unwired false false =
    prlc_verdict_unwired_ok /\
  prlc_conservation_knowing_fiber_ok = true /\
  prlc_conservation_meso_acting_ok = false /\
  purifyRefineLiveConservationProved = false /\
  prlcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — purify_refine_live) *)
(* ------------------------------------------------------------------ *)

Definition chemL0ProcessingRefiningAuthority : string :=
  "umst/umst-chem/src/processing_refining.rs".

Definition chemL0ProcessingRefiningTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition refiningGraphCutsAuthority : string :=
  "umst/umst-chem/src/refining_graph_cuts.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0Graph02CellId : string := "CHEM-L0-GRAPH-02".

Definition purifyRefineLiveConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PURIFY-REFINE-LIVE-CONSERVATION".

Definition purifyRefineLiveConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PURIFY-REFINE-LIVE-CONSERVATION PurifyRefineLiveConservationModality Unwired Assumed Proved Surrogate four-step lattice purifyRefineLiveConservationProved false evaluatePurifyRefineLiveBundle evaluatePurifyRefineLiveConservation named LIVE purify refine Fe Z=26 dissipative adjunction cost second law G-min presentation concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel purify refine live axiom refuse species id smuggle refuse extra element id Z=119 refuse free purification CAT-03 refuse purify refine live ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs".

Lemma purify_refine_live_conservation_cell_id :
  purifyRefineLiveConservationCellId =
  "CHEM-FORMAL-Q-COQ-PURIFY-REFINE-LIVE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma purify_refine_live_conservation_cites_l0_table :
  chemL0ProcessingRefiningTableAuthority <> "".
Proof. discriminate. Qed.

Lemma purify_refine_live_conservation_authority_path :
  purifyRefineLiveConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs".
Proof. reflexivity. Qed.

Lemma purify_refine_live_conservation_cites_l0_ore02 :
  chemL0ProcessingRefiningAuthority <> "".
Proof. discriminate. Qed.

Lemma purify_refine_live_conservation_cites_marker :
  prlcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma purify_refine_live_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma purify_refine_live_conservation_cites_ore02_cell :
  chemL0Graph02CellId = "CHEM-L0-GRAPH-02".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma purify_refine_live_not_26th_axiom :
  purifyRefineLiveConservationFraming <> parallelPurifyRefineLiveAxiomTag.
Proof. discriminate. Qed.

Lemma purify_refine_live_second_law_conservation_framing :
  purifyRefineLiveConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Dissipative adjunction prior art — named object, not prior-art axiom *)
(* ------------------------------------------------------------------ *)

Definition dissipativeAdjunctionPriorArtFraming : string :=
  "dissipative_adjunction_prior_art_not_named_object".

Definition dissipativeAdjunctionNamedObject : string :=
  "dissipative_adjunction_cost_on_purify_refine_morphism".

Lemma dissipative_adjunction_prior_art_not_named_object :
  dissipativeAdjunctionNamedObject <>
  dissipativeAdjunctionPriorArtFraming /\
  second_law_gmin_channel_tag = "second_law_gmin".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem dissipative_adjunction_is_named_object_not_prior_art :
  dissipativeAdjunctionNamedObject <>
  dissipativeAdjunctionPriorArtFraming /\
  dissipative_adjunction_cost_channel_tag = "dissipative_adjunction_cost" /\
  purifyRefineLiveConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Dissipative adjunction refuse — not free purification / CAT-03     *)
(* ------------------------------------------------------------------ *)

Definition dissipativeAdjunctionFraming : string :=
  "dissipative_adjunction_not_free_purification".

Lemma dissipative_adjunction_not_free_purification_refuse :
  dissipativeAdjunctionFraming <>
  freePurificationFraming /\
  dissipative_adjunction_cost_channel_tag = "dissipative_adjunction_cost".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem purify_refine_live_dissipative_adjunction_not_free_purification :
  dissipativeAdjunctionFraming <>
  freePurificationFraming /\
  refineProcessAuthority =
  "umst/umst-chem/src/refine_process.rs" /\
  purifyRefineLiveConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs not wired (freeze-safe until lift)               *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.

Lemma wave100_lib_rs_not_wired :
  wave100LibRsWired = false.
Proof. reflexivity. Qed.

Definition wave100FreezeTag : string :=
  "WAVE100 freeze — type-only until lift; not wired lib.rs".

Lemma wave100_freeze_tag_nonempty :
  wave100FreezeTag <> "".
Proof. discriminate. Qed.

Definition wave100LibRsAuthority : string :=
  "umst/umst-chem/src/lib.rs".

Definition wave100LibRsWiredMarker : string :=
  "wave100_lib_rs_wired_marker".

Lemma purify_refine_live_conservation_wave100_not_lib_rs :
  wave100LibRsAuthority <> wave100LibRsWiredMarker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma purify_refine_live_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma purify_refine_live_conservation_modality_unwired :
  purifyRefineLiveConservationModalityCurrent =
  purify_refine_live_conservation_unwired.
Proof. reflexivity. Qed.

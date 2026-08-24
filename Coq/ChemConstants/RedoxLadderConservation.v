(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: RedoxLadderConservation.v                             *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 17 **redox_ladder** **conservation**.     *)
(*  Redox ladder is Z-keyed equilibrium thermo vs kinetics remainder   *)
(*  on the same second-law + conservation object (not a parallel redox *)
(*  axiom / extra force). Pourbaix G(pH,E) ≠ corrosion rate.          *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  μ/T/P are graph functions v14 — not bare float pins.             *)
(*  redoxLadderConservationProved false. Modality Unwired.             *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/redox_ladder.rs (read-only cite). *)
(*  INT: umst/umst-chem/src/redox_interact_ladder.rs (read-only cite).  *)
(*  INT: umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs. *)
(*  PatternProductConservation.v cited.                                  *)
(*  WAVE100: no cabal/lakefile/lib.rs/eos.rs.                           *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-17 **redox_ladder** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive RedoxLadderConservationModality : Type :=
  | redox_ladder_conservation_unwired
  | redox_ladder_conservation_assumed
  | redox_ladder_conservation_proved
  | redox_ladder_conservation_surrogate.

Definition redoxLadderConservationModalityCurrent :
  RedoxLadderConservationModality :=
  redox_ladder_conservation_unwired.

Definition redox_ladder_lattice_cardinality : nat := 4.

Lemma redox_ladder_lattice_cardinality_is_four :
  redox_ladder_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma redox_ladder_lattice_not_118_squared :
  negb (Nat.eqb redox_ladder_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold redox_ladder_lattice_cardinality.
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

(* North-star §2 class 17 — redox_ladder concurrent Π_c factor. *)
Definition pattern_class_redox_ladder_idx : nat := 17.

Lemma pattern_class_redox_ladder_idx_is_17 :
  pattern_class_redox_ladder_idx = 17.
Proof. reflexivity. Qed.

Lemma redox_ladder_class_index_valid :
  pattern_class_index_valid pattern_class_redox_ladder_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_redox_ladder_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierRedoxLadderRowId : string := "X17".

Lemma cross_classifier_redox_ladder_row_named :
  crossClassifierRedoxLadderRowId = "X17".
Proof. reflexivity. Qed.

Definition pattern_class_redox_ladder_tag : string :=
  "redox_ladder".

Definition north_star_class_17_redox_ladder_tag : string :=
  "class 17 redox ladders".

Lemma pattern_class_redox_ladder_tag_nonempty :
  pattern_class_redox_ladder_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_17_redox_ladder_tag_nonempty :
  north_star_class_17_redox_ladder_tag <> "".
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

Definition redox_ladder_factor_tag : string :=
  "redox_ladder".

Definition equilibrium_pourbaix_channel_tag : string := "equilibrium_pourbaix".

Definition kinetics_remainder_channel_tag : string := "kinetics_remainder".

Lemma redox_ladder_factor_tag_nonempty :
  redox_ladder_factor_tag <> "".
Proof. discriminate. Qed.

Lemma equilibrium_pourbaix_channel_tag_nonempty :
  equilibrium_pourbaix_channel_tag <> "".
Proof. discriminate. Qed.

Lemma kinetics_remainder_channel_tag_nonempty :
  kinetics_remainder_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive rlc_channel_slot : Type :=
  | rlc_slot_unwired
  | rlc_slot_absent
  | rlc_slot_present.

Definition rlc_channel_slot_beq (s1 s2 : rlc_channel_slot) : bool :=
  match s1, s2 with
  | rlc_slot_unwired, rlc_slot_unwired => true
  | rlc_slot_absent, rlc_slot_absent => true
  | rlc_slot_present, rlc_slot_present => true
  | _, _ => false
  end.

Definition rlc_channel_slot_is_present (s : rlc_channel_slot) : bool :=
  match s with
  | rlc_slot_present => true
  | _ => false
  end.

Definition redoxLadderProductChannelCount : nat := 3.

Lemma redox_ladder_product_channel_count_is_three :
  redoxLadderProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = Pourbaix G(pH,E) equilibrium, 2 = class 17 redox_ladder. *)
Definition rlc_channel_equilibrium_pourbaix : nat := 0.
Definition rlc_channel_kinetics_remainder : nat := 1.
Definition rlc_channel_class17_redox_ladder : nat := 2.

Lemma rlc_channel_equilibrium_pourbaix_idx_is_0 :
  rlc_channel_equilibrium_pourbaix = 0.
Proof. reflexivity. Qed.

Lemma rlc_channel_kinetics_remainder_idx_is_1 :
  rlc_channel_kinetics_remainder = 1.
Proof. reflexivity. Qed.

Lemma rlc_channel_class17_redox_ladder_idx_is_2 :
  rlc_channel_class17_redox_ladder = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition rlc_channel_bundle : Type := nat -> rlc_channel_slot.

Definition redoxLadderBundleAllUnwired : rlc_channel_bundle :=
  fun _ => rlc_slot_unwired.

Definition redoxLadderBundleAt (b : rlc_channel_bundle) (idx : nat)
  (slot : rlc_channel_slot) : rlc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition redoxLadderBundleWithPresent
  (b : rlc_channel_bundle) (idx : nat) : rlc_channel_bundle :=
  redoxLadderBundleAt b idx rlc_slot_present.

Fixpoint count_rlc_present_up_to (b : rlc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if rlc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_rlc_present_up_to b i + add
  end.

Definition redoxLadderBundlePresentCount (b : rlc_channel_bundle) : nat :=
  count_rlc_present_up_to b redoxLadderProductChannelCount.

Definition redoxLadderBundleHolds (b : rlc_channel_bundle) (idx : nat) : bool :=
  rlc_channel_slot_is_present (b idx).

Definition redoxLadderBundleIsConcurrentProduct (b : rlc_channel_bundle) : bool :=
  Nat.leb 2 (redoxLadderBundlePresentCount b).

(* Fe Z=26 interact restriction + G-min + class 17 redox_ladder concurrent witness. *)
Definition redoxLadderFe26Witness : rlc_channel_bundle :=
  redoxLadderBundleWithPresent
    (redoxLadderBundleWithPresent
      (redoxLadderBundleWithPresent redoxLadderBundleAllUnwired
        rlc_channel_equilibrium_pourbaix)
      rlc_channel_kinetics_remainder)
    rlc_channel_class17_redox_ladder.

Definition redoxLadderEmptyWitness : rlc_channel_bundle :=
  redoxLadderBundleAllUnwired.

Definition redoxLadderSinglePresent : rlc_channel_bundle :=
  redoxLadderBundleWithPresent redoxLadderBundleAllUnwired
    rlc_channel_equilibrium_pourbaix.

Lemma equilibrium_pourbaix_channel_present :
  redoxLadderBundleHolds redoxLadderFe26Witness
    rlc_channel_equilibrium_pourbaix = true.
Proof. reflexivity. Qed.

Lemma kinetics_remainder_channel_present :
  redoxLadderBundleHolds redoxLadderFe26Witness
    rlc_channel_kinetics_remainder = true.
Proof. reflexivity. Qed.

Lemma class17_redox_ladder_channel_present :
  redoxLadderBundleHolds redoxLadderFe26Witness
    rlc_channel_class17_redox_ladder = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  redoxLadderBundlePresentCount redoxLadderFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  redoxLadderBundleIsConcurrentProduct redoxLadderFe26Witness = true.
Proof.
  unfold redoxLadderBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  redoxLadderBundlePresentCount redoxLadderEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  redoxLadderBundleIsConcurrentProduct redoxLadderEmptyWitness = false.
Proof.
  unfold redoxLadderBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  redoxLadderBundlePresentCount redoxLadderSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  redoxLadderBundleIsConcurrentProduct redoxLadderSinglePresent = false.
Proof.
  unfold redoxLadderBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive rlc_xor_posture : Type :=
  | rlc_xor_exclusive
  | rlc_xor_concurrent_product.

Definition rlcXorClassifierMarker : string := "chem_l0_redox_ladder_xor_classifier_v1".
Definition rlcConcurrentProductMarker : string := "chem_int_redox_ladder_product_v1".

Lemma rlc_xor_marker_ne_concurrent_product_marker :
  rlcXorClassifierMarker <> rlcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition rlcXorClassifierIncompatible (claim_xor : bool)
  (b : rlc_channel_bundle) : bool :=
  claim_xor && redoxLadderBundleIsConcurrentProduct b.

Lemma rlc_xor_refuse_on_fe26_witness :
  rlcXorClassifierIncompatible true redoxLadderFe26Witness = true.
Proof.
  unfold rlcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma rlc_xor_ok_on_concurrent_product_claim :
  rlcXorClassifierIncompatible false redoxLadderFe26Witness = false.
Proof. reflexivity. Qed.

Definition rlcProductNotXor : bool :=
  redoxLadderBundleIsConcurrentProduct redoxLadderFe26Witness &&
  rlcXorClassifierIncompatible true redoxLadderFe26Witness.

Lemma rlc_product_not_xor_true : rlcProductNotXor = true.
Proof.
  unfold rlcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  rlcProductNotXor = true /\
  Nat.leb 2 (redoxLadderBundlePresentCount
    redoxLadderFe26Witness) = true /\
  rlcXorClassifierMarker <> rlcConcurrentProductMarker.
Proof.
  split.
  - apply rlc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply rlc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive rlc_bar_presence : Type :=
  | rlc_bar_absent
  | rlc_bar_present.

Record rlc_claim_bar : Type := {
  rlc_bar_presence_field : rlc_bar_presence;
  rlc_bar_defect_total : nat
}.

Definition redoxLadderClaimBarAbsent : rlc_claim_bar :=
  {| rlc_bar_presence_field := rlc_bar_absent;
     rlc_bar_defect_total := 0 |}.

Definition redoxLadderClaimBarZeroDefect : rlc_claim_bar :=
  {| rlc_bar_presence_field := rlc_bar_present;
     rlc_bar_defect_total := 0 |}.

Definition rlc_claim_bar_zero_defect (b : rlc_claim_bar) : bool :=
  match rlc_bar_presence_field b with
  | rlc_bar_absent => false
  | rlc_bar_present => Nat.eqb (rlc_bar_defect_total b) 0
  end.

Lemma rlc_claim_bar_zero_defect_true :
  rlc_claim_bar_zero_defect redoxLadderClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma rlc_claim_bar_absent_not_zero_defect :
  rlc_claim_bar_zero_defect redoxLadderClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive rlc_conservation_verdict : Type :=
  | rlc_verdict_unwired_ok
  | rlc_verdict_named_ok
  | rlc_verdict_design_ok
  | rlc_verdict_trivial_refuse
  | rlc_verdict_xor_refuse
  | rlc_verdict_green_invent_refuse
  | rlc_verdict_proved_without_bar_refuse
  | rlc_verdict_production_wired_refuse
  | rlc_verdict_parallel_redox_axiom_refuse
  | rlc_verdict_species_id_smuggle_refuse
  | rlc_verdict_extra_element_id_refuse
  | rlc_verdict_parallel_redox_axiom_force_refuse
  | rlc_verdict_mtp_graph_function_float_pin_refuse.

Definition rlc_conservation_verdict_ok (v : rlc_conservation_verdict) : bool :=
  match v with
  | rlc_verdict_unwired_ok => true
  | rlc_verdict_named_ok => true
  | rlc_verdict_design_ok => true
  | _ => false
  end.

Definition redoxLadderBundleNontrivial (b : rlc_channel_bundle) : bool :=
  Nat.ltb 0 (redoxLadderBundlePresentCount b).

Definition evaluate_redox_ladder_bundle
  (m : RedoxLadderConservationModality)
  (b : rlc_channel_bundle)
  (bar : rlc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : rlc_conservation_verdict :=
  if claim_physics_green
  then rlc_verdict_green_invent_refuse
  else if claim_proved
       then rlc_verdict_proved_without_bar_refuse
       else if negb (redoxLadderBundleNontrivial b)
            then rlc_verdict_trivial_refuse
            else if rlcXorClassifierIncompatible claim_xor_classifier b
                 then rlc_verdict_xor_refuse
                 else
                   match m with
                   | redox_ladder_conservation_unwired =>
                       if redoxLadderBundleIsConcurrentProduct b
                       then rlc_verdict_named_ok
                       else rlc_verdict_design_ok
                   | redox_ladder_conservation_assumed
                   | redox_ladder_conservation_surrogate =>
                       rlc_verdict_design_ok
                   | redox_ladder_conservation_proved =>
                       rlc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_redox_ladder_conservation_close
  (m : RedoxLadderConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : rlc_conservation_verdict :=
  if claim_physics_green
  then rlc_verdict_green_invent_refuse
  else if claim_production_wired
  then rlc_verdict_production_wired_refuse
  else
    match m with
    | redox_ladder_conservation_unwired => rlc_verdict_unwired_ok
    | redox_ladder_conservation_assumed
    | redox_ladder_conservation_proved
    | redox_ladder_conservation_surrogate => rlc_verdict_named_ok
    end.

Definition redox_ladder_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_redox_ladder_conservation_close
          redox_ladder_conservation_proved claim_physics_green claim_production_wired with
  | rlc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive rlc_conservation_law : Type :=
  | rlc_law_conserved
  | rlc_law_named_ok
  | rlc_law_trivial_refuse
  | rlc_law_green_invent_refuse.

Definition rlc_conservation_law_count : nat := 4.

Lemma rlc_conservation_law_count_is_four :
  rlc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive rlc_conservation_law_witness : Type :=
  | rlc_law_witness_open
  | rlc_law_witness_proved.

Definition evaluate_rlc_conservation_law_witness
  (law : rlc_conservation_law)
  (m : RedoxLadderConservationModality)
  : rlc_conservation_law_witness :=
  match m with
  | redox_ladder_conservation_unwired
  | redox_ladder_conservation_assumed
  | redox_ladder_conservation_surrogate => rlc_law_witness_open
  | redox_ladder_conservation_proved => rlc_law_witness_proved
  end.

Lemma all_rlc_conservation_laws_open_at_unwired :
  evaluate_rlc_conservation_law_witness rlc_law_conserved
    redox_ladder_conservation_unwired = rlc_law_witness_open /\
  evaluate_rlc_conservation_law_witness rlc_law_named_ok
    redox_ladder_conservation_unwired = rlc_law_witness_open /\
  evaluate_rlc_conservation_law_witness rlc_law_trivial_refuse
    redox_ladder_conservation_unwired = rlc_law_witness_open /\
  evaluate_rlc_conservation_law_witness rlc_law_green_invent_refuse
    redox_ladder_conservation_unwired = rlc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-17 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition redoxLadderConservationProved : bool := false.

Lemma redox_ladder_conservation_proved_false :
  redoxLadderConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_unwired false false =
  rlc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_unwired false false =
  rlc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_unwired false false) =
  true.
Proof.
  unfold rlc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false false =
  rlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_redox_ladder_conservation :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false false =
  rlc_verdict_named_ok /\
  redoxLadderBundleIsConcurrentProduct redoxLadderFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_redox_ladder_idx = 17.
Proof.
  repeat split; reflexivity.
Qed.

Lemma rlc_named_close_ok :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_proved false false =
  rlc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_redox_ladder_conservation_close :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_proved false false =
  rlc_verdict_named_ok /\
  redox_ladder_conservation_authorized false false = true.
Proof.
  split.
  - apply rlc_named_close_ok.
  - unfold redox_ladder_conservation_authorized.
    rewrite rlc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — redox_ladder refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderEmptyWitness
    redoxLadderClaimBarAbsent false false false =
  rlc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderEmptyWitness
    redoxLadderClaimBarAbsent false false false =
  rlc_verdict_trivial_refuse /\
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_bundle
       redox_ladder_conservation_unwired
       redoxLadderEmptyWitness
       redoxLadderClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold rlc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent true false false =
  rlc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent true false false =
  rlc_verdict_xor_refuse /\
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_bundle
       redox_ladder_conservation_unwired
       redoxLadderFe26Witness
       redoxLadderClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold rlc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_unwired true false =
  rlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_unwired true false) =
  false.
Proof.
  unfold rlc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_rlc_bundle_refuse :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false true false =
  rlc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — redox_ladder refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false true =
  rlc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false true =
  rlc_verdict_proved_without_bar_refuse /\
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_bundle
       redox_ladder_conservation_unwired
       redoxLadderFe26Witness
       redoxLadderClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold rlc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — redox_ladder lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_proved false true =
  rlc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_proved false true) =
  false.
Proof.
  unfold rlc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel redox_ladder axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition redoxLadderConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/redox_ladder.rs".

Definition parallelRedoxAxiomTag : string := "26th_chemistry_redox_axiom".

Lemma parallel_redox_axiom_refuse :
  redoxLadderConservationAuthority <>
  parallelRedoxAxiomTag /\
  redoxLadderConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply redox_ladder_conservation_proved_false.
Qed.

Theorem parallel_redox_axiom_not_minted :
  redoxLadderConservationAuthority =
  "umst/umst-chem/src/l0_tables/redox_ladder.rs" /\
  redoxLadderConservationProved = false /\
  redoxLadderConservationAuthority <> parallelRedoxAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — equilibrium Pourbaix ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "pourbaix_equilibrium_not_rate_object".

Definition redoxLadderConservationFraming : string :=
  "second_law_conservation_redox_ladder_equilibrium_pourbaix_one_axiom".

Lemma species_id_smuggle_refuse :
  redoxLadderConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_redox_ladder_idx = 17.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem equilibrium_pourbaix_not_species_id_smuggle :
  redoxLadderConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_redox_ladder_idx = 17 /\
  redoxLadderConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — redox_ladder ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "pourbaix_equilibrium_is_corrosion_rate".

Lemma extra_element_id_refuse :
  redoxLadderConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  redoxLadderConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — redox_ladder ≠ extra redox_ladder force axiom    *)
(* ------------------------------------------------------------------ *)

Definition parallelRedoxAxiomFraming : string :=
  "parallel_redox_axiom_minted_as_26th_law".

Definition pourbaixNotCorrosionRateAuthority : string :=
  "umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs".

Lemma parallel_redox_axiom_force_refuse :
  redoxLadderConservationFraming <>
  parallelRedoxAxiomFraming /\
  pourbaixNotCorrosionRateAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem redox_ladder_not_parallel_redox_ladder_force :
  redoxLadderConservationFraming <>
  parallelRedoxAxiomFraming /\
  pourbaixNotCorrosionRateAuthority =
  "umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs" /\
  redoxLadderConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition mtpGraphFunctionFloatPinFraming : string :=
  "bare_float_pins_on_mu_t_p_redox_ladder_pourbaix_scaffold".

Lemma mtp_graph_function_float_pin_refuse :
  redoxLadderConservationFraming <>
  mtpGraphFunctionFloatPinFraming /\
  equilibrium_pourbaix_channel_tag = "equilibrium_pourbaix".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem mtp_graph_function_not_float_pin :
  redoxLadderConservationFraming <>
  mtpGraphFunctionFloatPinFraming /\
  kinetics_remainder_channel_tag = "kinetics_remainder" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  RedoxLadder **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition rlc_conservation_coherence_scaffold : bool :=
  rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_proved false false) &&
  negb (rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_unwired true false)) &&
  negb (rlc_conservation_verdict_ok
    (evaluate_redox_ladder_conservation_close
       redox_ladder_conservation_proved false true)).

Lemma rlc_conservation_coherence_scaffold_true :
  rlc_conservation_coherence_scaffold = true.
Proof.
  unfold rlc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem rlc_conservation_coherence_scaffold_theorem :
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_proved false false =
    rlc_verdict_named_ok /\
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_unwired true false =
    rlc_verdict_green_invent_refuse /\
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_proved false true =
    rlc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition rlc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition rlc_conservation_knowing_fiber_ok : bool :=
  rlc_conservation_fiber_ok fiber_quantum_knowing.

Definition rlc_conservation_meso_acting_ok : bool :=
  rlc_conservation_fiber_ok fiber_meso_acting.

Lemma rlc_conservation_knowing_fiber_ok_true :
  rlc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma rlc_conservation_meso_acting_not_ok :
  rlc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem rlc_conservation_routes_knowing_not_meso :
  rlc_conservation_knowing_fiber_ok = true /\
  rlc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply rlc_conservation_knowing_fiber_ok_true.
  - apply rlc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  rlc_conservation_knowing_fiber_ok &&
  negb rlc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, rlc_conservation_knowing_fiber_ok,
    rlc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-17 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem redox_ladder_conservation_fixture_scaffold :
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false false =
    rlc_verdict_named_ok /\
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderEmptyWitness
    redoxLadderClaimBarAbsent false false false =
    rlc_verdict_trivial_refuse /\
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent true false false =
    rlc_verdict_xor_refuse /\
  evaluate_redox_ladder_bundle
    redox_ladder_conservation_unwired
    redoxLadderFe26Witness
    redoxLadderClaimBarAbsent false false true =
    rlc_verdict_proved_without_bar_refuse /\
  evaluate_redox_ladder_conservation_close
    redox_ladder_conservation_unwired false false =
    rlc_verdict_unwired_ok /\
  rlc_conservation_knowing_fiber_ok = true /\
  rlc_conservation_meso_acting_ok = false /\
  redoxLadderConservationProved = false /\
  rlcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.


Definition chemicalPotentialGraphFunctionAuthority : string :=
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs".

Definition temperatureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/temperature_is_graph_function.rs".

Definition pressureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/pressure_is_graph_function.rs".

Definition chemIntNuanceRedoxCellId : string := "CHEM-INT-NUANCE-REDOX".

Definition chemIntPourbaixNotCorrosionRateCellId : string :=
  "CHEM-INT-POURBAIX-NOT-CORROSION-RATE".

Lemma redox_ladder_conservation_cites_nuance_cell :
  chemIntNuanceRedoxCellId = "CHEM-INT-NUANCE-REDOX".
Proof. reflexivity. Qed.

Lemma redox_ladder_conservation_cites_pourbaix_remainder :
  pourbaixNotCorrosionRateAuthority <>
  "".
Proof. discriminate. Qed.

Lemma redox_ladder_conservation_cites_mtp_graph_functions :
  chemicalPotentialGraphFunctionAuthority <> "" /\
  temperatureGraphFunctionAuthority <> "" /\
  pressureGraphFunctionAuthority <> "".
Proof. repeat split; discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — redox_ladder) *)
(* ------------------------------------------------------------------ *)

Definition chemL0RedoxLadderAuthority : string :=
  "umst/umst-chem/src/l0_tables/redox_ladder.rs".

Definition chemL0RedoxLadderTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/redox_ladder.rs".

Definition redoxInteractLadderAuthority : string :=
  "umst/umst-chem/src/redox_interact_ladder.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeRedoxCellId : string := "CHEM-L0-EDGE-REDOX".

Definition redoxLadderConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-REDOX-LADDER-CONSERVATION".

Definition redoxLadderConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-REDOX-LADDER-CONSERVATION RedoxLadderConservationModality Unwired Assumed Proved Surrogate four-step lattice redoxLadderConservationProved false evaluateRedoxLadderBundle evaluateRedoxLadderConservation named class 17 redox ladder Fe Z=26 equilibrium Pourbaix G(pH,E) kinetics remainder second law concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel redox axiom refuse species id smuggle refuse extra element id Z=119 refuse parallel redox axiom force refuse redox ladder ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired μ T P graph functions v14 not float pins Pourbaix equilibrium not corrosion rate WAVE100 no lib.rs no eos.rs".

Lemma redox_ladder_conservation_cell_id :
  redoxLadderConservationCellId =
  "CHEM-FORMAL-Q-COQ-REDOX-LADDER-CONSERVATION".
Proof. reflexivity. Qed.

Lemma redox_ladder_conservation_cites_l0_table :
  chemL0RedoxLadderTableAuthority <> "".
Proof. discriminate. Qed.

Lemma redox_ladder_conservation_authority_path :
  redoxLadderConservationAuthority =
  "umst/umst-chem/src/l0_tables/redox_ladder.rs".
Proof. reflexivity. Qed.

Lemma redox_ladder_conservation_cites_l0_ore02 :
  chemL0RedoxLadderAuthority <> "".
Proof. discriminate. Qed.

Lemma redox_ladder_conservation_cites_marker :
  rlcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma redox_ladder_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma redox_ladder_conservation_cites_ore02_cell :
  chemL0EdgeRedoxCellId = "CHEM-L0-EDGE-REDOX".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma redox_ladder_not_26th_axiom :
  redoxLadderConservationFraming <> parallelRedoxAxiomTag.
Proof. discriminate. Qed.

Lemma redox_ladder_second_law_conservation_framing :
  redoxLadderConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Pourbaix G(pH,E) equilibrium — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition pourbaixEquilibriumFraming : string :=
  "pourbaix_g_ph_e_equilibrium_not_corrosion_rate".

Definition equilibriumPourbaixNamedObject : string :=
  "equilibrium_pourbaix_on_redox_ladder_morphism".

Lemma pourbaix_equilibrium_not_rate_object :
  equilibriumPourbaixNamedObject <>
  pourbaixEquilibriumFraming /\
  kinetics_remainder_channel_tag = "kinetics_remainder".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem equilibrium_pourbaix_is_named_object_not_tst :
  equilibriumPourbaixNamedObject <>
  pourbaixEquilibriumFraming /\
  equilibrium_pourbaix_channel_tag = "equilibrium_pourbaix" /\
  redoxLadderConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not redox_ladder axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition equilibriumPourbaixFraming : string :=
  "equilibrium_pourbaix_not_rate_force".

Lemma equilibrium_pourbaix_not_rate_force_refuse :
  equilibriumPourbaixFraming <>
  parallelRedoxAxiomFraming /\
  equilibrium_pourbaix_channel_tag = "equilibrium_pourbaix".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem redox_ladder_equilibrium_pourbaix_not_corrosion_rate :
  equilibriumPourbaixFraming <>
  parallelRedoxAxiomFraming /\
  pourbaixNotCorrosionRateAuthority =
  "umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs" /\
  redoxLadderConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma redox_ladder_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma redox_ladder_conservation_modality_unwired :
  redoxLadderConservationModalityCurrent =
  redox_ladder_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ImpureComponentMorphismConservation.v               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 8 **impure_component_morphism**             *)
(*  **conservation**. Impurity is a morphism on the same second-law +  *)
(*  conservation object (component in an assemblage), not a second     *)
(*  SpeciesId / 26th axiom. Concurrent Π_c PatternBundle factor —       *)
(*  **product** not XOR. impureComponentMorphismConservationProved       *)
(*  false. Modality Unwired.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/impure_component_morphism.rs (read-only). *)
(*  INT: umst/umst-chem/src/l0_tables/impure_component_morphism.rs      *)
(*  (read-only cite). PatternProductConservation.v posture cited.       *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-8 **impure_component_morphism** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive ImpureComponentMorphismConservationModality : Type :=
  | impure_component_morphism_conservation_unwired
  | impure_component_morphism_conservation_assumed
  | impure_component_morphism_conservation_proved
  | impure_component_morphism_conservation_surrogate.

Definition impureComponentMorphismConservationModalityCurrent :
  ImpureComponentMorphismConservationModality :=
  impure_component_morphism_conservation_unwired.

Definition impure_component_morphism_lattice_cardinality : nat := 4.

Lemma impure_component_morphism_lattice_cardinality_is_four :
  impure_component_morphism_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma impure_component_morphism_lattice_not_118_squared :
  negb (Nat.eqb impure_component_morphism_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold impure_component_morphism_lattice_cardinality.
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

(* North-star §2 class 8 — impure_component_morphism concurrent Π_c factor. *)
Definition pattern_class_impure_component_morphism_idx : nat := 8.

Lemma pattern_class_impure_component_morphism_idx_is_8 :
  pattern_class_impure_component_morphism_idx = 8.
Proof. reflexivity. Qed.

Lemma impure_component_morphism_class_index_valid :
  pattern_class_index_valid pattern_class_impure_component_morphism_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_impure_component_morphism_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierImpureComponentMorphismRowId : string := "X08".

Lemma cross_classifier_impure_component_morphism_row_named :
  crossClassifierImpureComponentMorphismRowId = "X08".
Proof. reflexivity. Qed.

Definition pattern_class_impure_component_morphism_tag : string :=
  "impure_component_morphism".

Definition north_star_class_8_impure_component_tag : string :=
  "class 8 impure component morphism".

Lemma pattern_class_impure_component_morphism_tag_nonempty :
  pattern_class_impure_component_morphism_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_8_impure_component_tag_nonempty :
  north_star_class_8_impure_component_tag <> "".
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

Definition impure_component_morphism_factor_tag : string :=
  "impure_component_morphism".

Definition ore_constituent_morphism_channel_tag : string := "ore_constituent_morphism".

Definition second_law_gmin_channel_tag : string := "second_law_presentation".

Lemma impure_component_morphism_factor_tag_nonempty :
  impure_component_morphism_factor_tag <> "".
Proof. discriminate. Qed.

Lemma ore_constituent_morphism_channel_tag_nonempty :
  ore_constituent_morphism_channel_tag <> "".
Proof. discriminate. Qed.

Lemma second_law_gmin_channel_tag_nonempty :
  second_law_gmin_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive icm_channel_slot : Type :=
  | icm_slot_unwired
  | icm_slot_absent
  | icm_slot_present.

Definition icm_channel_slot_beq (s1 s2 : icm_channel_slot) : bool :=
  match s1, s2 with
  | icm_slot_unwired, icm_slot_unwired => true
  | icm_slot_absent, icm_slot_absent => true
  | icm_slot_present, icm_slot_present => true
  | _, _ => false
  end.

Definition icm_channel_slot_is_present (s : icm_channel_slot) : bool :=
  match s with
  | icm_slot_present => true
  | _ => false
  end.

Definition impureComponentMorphismProductChannelCount : nat := 3.

Lemma impure_component_morphism_product_channel_count_is_three :
  impureComponentMorphismProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = ore constituent morphism, 1 = G-min second law, 2 = class 8. *)
Definition icm_channel_ore_constituent_morphism : nat := 0.
Definition icm_channel_second_law_gmin : nat := 1.
Definition icm_channel_class8_impure_morphism : nat := 2.

Lemma icm_channel_ore_constituent_morphism_idx_is_0 :
  icm_channel_ore_constituent_morphism = 0.
Proof. reflexivity. Qed.

Lemma icm_channel_second_law_gmin_idx_is_1 :
  icm_channel_second_law_gmin = 1.
Proof. reflexivity. Qed.

Lemma icm_channel_class8_impure_morphism_idx_is_2 :
  icm_channel_class8_impure_morphism = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition icm_channel_bundle : Type := nat -> icm_channel_slot.

Definition impureComponentMorphismBundleAllUnwired : icm_channel_bundle :=
  fun _ => icm_slot_unwired.

Definition impureComponentMorphismBundleAt (b : icm_channel_bundle) (idx : nat)
  (slot : icm_channel_slot) : icm_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition impureComponentMorphismBundleWithPresent
  (b : icm_channel_bundle) (idx : nat) : icm_channel_bundle :=
  impureComponentMorphismBundleAt b idx icm_slot_present.

Fixpoint count_icm_present_up_to (b : icm_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if icm_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_icm_present_up_to b i + add
  end.

Definition impureComponentMorphismBundlePresentCount (b : icm_channel_bundle) : nat :=
  count_icm_present_up_to b impureComponentMorphismProductChannelCount.

Definition impureComponentMorphismBundleHolds (b : icm_channel_bundle) (idx : nat) : bool :=
  icm_channel_slot_is_present (b idx).

Definition impureComponentMorphismBundleIsConcurrentProduct (b : icm_channel_bundle) : bool :=
  Nat.leb 2 (impureComponentMorphismBundlePresentCount b).

(* Fe Z=26 ore constituent + G-min + class-8 impure morphism concurrent witness. *)
Definition impureComponentMorphismFe26Witness : icm_channel_bundle :=
  impureComponentMorphismBundleWithPresent
    (impureComponentMorphismBundleWithPresent
      (impureComponentMorphismBundleWithPresent impureComponentMorphismBundleAllUnwired
        icm_channel_ore_constituent_morphism)
      icm_channel_second_law_gmin)
    icm_channel_class8_impure_morphism.

Definition impureComponentMorphismEmptyWitness : icm_channel_bundle :=
  impureComponentMorphismBundleAllUnwired.

Definition impureComponentMorphismSinglePresent : icm_channel_bundle :=
  impureComponentMorphismBundleWithPresent impureComponentMorphismBundleAllUnwired
    icm_channel_ore_constituent_morphism.

Lemma ore_constituent_morphism_channel_present :
  impureComponentMorphismBundleHolds impureComponentMorphismFe26Witness
    icm_channel_ore_constituent_morphism = true.
Proof. reflexivity. Qed.

Lemma second_law_gmin_channel_present :
  impureComponentMorphismBundleHolds impureComponentMorphismFe26Witness
    icm_channel_second_law_gmin = true.
Proof. reflexivity. Qed.

Lemma class8_impure_morphism_channel_present :
  impureComponentMorphismBundleHolds impureComponentMorphismFe26Witness
    icm_channel_class8_impure_morphism = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  impureComponentMorphismBundlePresentCount impureComponentMorphismFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismFe26Witness = true.
Proof.
  unfold impureComponentMorphismBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  impureComponentMorphismBundlePresentCount impureComponentMorphismEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismEmptyWitness = false.
Proof.
  unfold impureComponentMorphismBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  impureComponentMorphismBundlePresentCount impureComponentMorphismSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismSinglePresent = false.
Proof.
  unfold impureComponentMorphismBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive icm_xor_posture : Type :=
  | icm_xor_exclusive
  | icm_xor_concurrent_product.

Definition icmXorClassifierMarker : string := "chem_l0_impure_component_xor_classifier_v1".
Definition icmConcurrentProductMarker : string := "chem_int_impure_component_product_v1".

Lemma icm_xor_marker_ne_concurrent_product_marker :
  icmXorClassifierMarker <> icmConcurrentProductMarker.
Proof. discriminate. Qed.

Definition icmXorClassifierIncompatible (claim_xor : bool)
  (b : icm_channel_bundle) : bool :=
  claim_xor && impureComponentMorphismBundleIsConcurrentProduct b.

Lemma icm_xor_refuse_on_fe26_witness :
  icmXorClassifierIncompatible true impureComponentMorphismFe26Witness = true.
Proof.
  unfold icmXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma icm_xor_ok_on_concurrent_product_claim :
  icmXorClassifierIncompatible false impureComponentMorphismFe26Witness = false.
Proof. reflexivity. Qed.

Definition icmProductNotXor : bool :=
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismFe26Witness &&
  icmXorClassifierIncompatible true impureComponentMorphismFe26Witness.

Lemma icm_product_not_xor_true : icmProductNotXor = true.
Proof.
  unfold icmProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  icmProductNotXor = true /\
  Nat.leb 2 (impureComponentMorphismBundlePresentCount
    impureComponentMorphismFe26Witness) = true /\
  icmXorClassifierMarker <> icmConcurrentProductMarker.
Proof.
  split.
  - apply icm_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply icm_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive icm_bar_presence : Type :=
  | icm_bar_absent
  | icm_bar_present.

Record icm_claim_bar : Type := {
  icm_bar_presence_field : icm_bar_presence;
  icm_bar_defect_total : nat
}.

Definition impureComponentMorphismClaimBarAbsent : icm_claim_bar :=
  {| icm_bar_presence_field := icm_bar_absent;
     icm_bar_defect_total := 0 |}.

Definition impureComponentMorphismClaimBarZeroDefect : icm_claim_bar :=
  {| icm_bar_presence_field := icm_bar_present;
     icm_bar_defect_total := 0 |}.

Definition icm_claim_bar_zero_defect (b : icm_claim_bar) : bool :=
  match icm_bar_presence_field b with
  | icm_bar_absent => false
  | icm_bar_present => Nat.eqb (icm_bar_defect_total b) 0
  end.

Lemma icm_claim_bar_zero_defect_true :
  icm_claim_bar_zero_defect impureComponentMorphismClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma icm_claim_bar_absent_not_zero_defect :
  icm_claim_bar_zero_defect impureComponentMorphismClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive icm_conservation_verdict : Type :=
  | icm_verdict_unwired_ok
  | icm_verdict_named_ok
  | icm_verdict_design_ok
  | icm_verdict_trivial_refuse
  | icm_verdict_xor_refuse
  | icm_verdict_green_invent_refuse
  | icm_verdict_proved_without_bar_refuse
  | icm_verdict_production_wired_refuse
  | icm_verdict_parallel_impure_morphism_axiom_refuse
  | icm_verdict_species_id_smuggle_refuse
  | icm_verdict_extra_element_id_refuse
  | icm_verdict_free_purification_refuse
  | icm_verdict_tp_float_pin_refuse.

Definition icm_conservation_verdict_ok (v : icm_conservation_verdict) : bool :=
  match v with
  | icm_verdict_unwired_ok => true
  | icm_verdict_named_ok => true
  | icm_verdict_design_ok => true
  | _ => false
  end.

Definition impureComponentMorphismBundleNontrivial (b : icm_channel_bundle) : bool :=
  Nat.ltb 0 (impureComponentMorphismBundlePresentCount b).

Definition evaluate_impure_component_morphism_bundle
  (m : ImpureComponentMorphismConservationModality)
  (b : icm_channel_bundle)
  (bar : icm_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : icm_conservation_verdict :=
  if claim_physics_green
  then icm_verdict_green_invent_refuse
  else if claim_proved
       then icm_verdict_proved_without_bar_refuse
       else if negb (impureComponentMorphismBundleNontrivial b)
            then icm_verdict_trivial_refuse
            else if icmXorClassifierIncompatible claim_xor_classifier b
                 then icm_verdict_xor_refuse
                 else
                   match m with
                   | impure_component_morphism_conservation_unwired =>
                       if impureComponentMorphismBundleIsConcurrentProduct b
                       then icm_verdict_named_ok
                       else icm_verdict_design_ok
                   | impure_component_morphism_conservation_assumed
                   | impure_component_morphism_conservation_surrogate =>
                       icm_verdict_design_ok
                   | impure_component_morphism_conservation_proved =>
                       icm_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_impure_component_morphism_conservation_close
  (m : ImpureComponentMorphismConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : icm_conservation_verdict :=
  if claim_physics_green
  then icm_verdict_green_invent_refuse
  else if claim_production_wired
  then icm_verdict_production_wired_refuse
  else
    match m with
    | impure_component_morphism_conservation_unwired => icm_verdict_unwired_ok
    | impure_component_morphism_conservation_assumed
    | impure_component_morphism_conservation_proved
    | impure_component_morphism_conservation_surrogate => icm_verdict_named_ok
    end.

Definition impure_component_morphism_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_impure_component_morphism_conservation_close
          impure_component_morphism_conservation_proved claim_physics_green claim_production_wired with
  | icm_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive icm_conservation_law : Type :=
  | icm_law_conserved
  | icm_law_named_ok
  | icm_law_trivial_refuse
  | icm_law_green_invent_refuse.

Definition icm_conservation_law_count : nat := 4.

Lemma icm_conservation_law_count_is_four :
  icm_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive icm_conservation_law_witness : Type :=
  | icm_law_witness_open
  | icm_law_witness_proved.

Definition evaluate_icm_conservation_law_witness
  (law : icm_conservation_law)
  (m : ImpureComponentMorphismConservationModality)
  : icm_conservation_law_witness :=
  match m with
  | impure_component_morphism_conservation_unwired
  | impure_component_morphism_conservation_assumed
  | impure_component_morphism_conservation_surrogate => icm_law_witness_open
  | impure_component_morphism_conservation_proved => icm_law_witness_proved
  end.

Lemma all_icm_conservation_laws_open_at_unwired :
  evaluate_icm_conservation_law_witness icm_law_conserved
    impure_component_morphism_conservation_unwired = icm_law_witness_open /\
  evaluate_icm_conservation_law_witness icm_law_named_ok
    impure_component_morphism_conservation_unwired = icm_law_witness_open /\
  evaluate_icm_conservation_law_witness icm_law_trivial_refuse
    impure_component_morphism_conservation_unwired = icm_law_witness_open /\
  evaluate_icm_conservation_law_witness icm_law_green_invent_refuse
    impure_component_morphism_conservation_unwired = icm_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-8 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition impureComponentMorphismConservationProved : bool := false.

Lemma impure_component_morphism_conservation_proved_false :
  impureComponentMorphismConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_unwired false false =
  icm_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_unwired false false =
  icm_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_unwired false false) =
  true.
Proof.
  unfold icm_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false false =
  icm_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_impure_component_morphism_conservation :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false false =
  icm_verdict_named_ok /\
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_impure_component_morphism_idx = 8.
Proof.
  repeat split; reflexivity.
Qed.

Lemma icm_named_close_ok :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_proved false false =
  icm_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_impure_component_morphism_conservation_close :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_proved false false =
  icm_verdict_named_ok /\
  impure_component_morphism_conservation_authorized false false = true.
Proof.
  split.
  - apply icm_named_close_ok.
  - unfold impure_component_morphism_conservation_authorized.
    rewrite icm_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — impure-component-morphism refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismEmptyWitness
    impureComponentMorphismClaimBarAbsent false false false =
  icm_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismEmptyWitness
    impureComponentMorphismClaimBarAbsent false false false =
  icm_verdict_trivial_refuse /\
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_bundle
       impure_component_morphism_conservation_unwired
       impureComponentMorphismEmptyWitness
       impureComponentMorphismClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold icm_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent true false false =
  icm_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent true false false =
  icm_verdict_xor_refuse /\
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_bundle
       impure_component_morphism_conservation_unwired
       impureComponentMorphismFe26Witness
       impureComponentMorphismClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold icm_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_unwired true false =
  icm_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_unwired true false) =
  false.
Proof.
  unfold icm_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_icm_bundle_refuse :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false true false =
  icm_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — impure-component-morphism refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false true =
  icm_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false true =
  icm_verdict_proved_without_bar_refuse /\
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_bundle
       impure_component_morphism_conservation_unwired
       impureComponentMorphismFe26Witness
       impureComponentMorphismClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold icm_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — impure-component-morphism lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_proved false true =
  icm_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_proved false true) =
  false.
Proof.
  unfold icm_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel impure-morphism axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition impureComponentMorphismConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs".

Definition parallelImpureMorphismAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_impure_morphism_axiom_refuse :
  impureComponentMorphismConservationAuthority <>
  parallelImpureMorphismAxiomTag /\
  impureComponentMorphismConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply impure_component_morphism_conservation_proved_false.
Qed.

Theorem parallel_impure_morphism_axiom_not_minted :
  impureComponentMorphismConservationAuthority =
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs" /\
  impureComponentMorphismConservationProved = false /\
  impureComponentMorphismConservationAuthority <> parallelImpureMorphismAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — ore constituent morphism ≠ L1 SpeciesId  *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition impureComponentMorphismConservationFraming : string :=
  "second_law_conservation_impure_component_morphism_one_axiom".

Lemma species_id_smuggle_refuse :
  impureComponentMorphismConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_impure_component_morphism_idx = 8.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ore_constituent_morphism_not_species_id_smuggle :
  impureComponentMorphismConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_impure_component_morphism_idx = 8 /\
  impureComponentMorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — impurity morphism ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  impureComponentMorphismConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  impureComponentMorphismConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — impure morphism ≠ CAT-03 adjunction     *)
(* ------------------------------------------------------------------ *)

Definition freePurificationFraming : string :=
  "free_purification_reverse_refine_cat03_adjunction".

Definition impurePureAdjunctionAuthority : string :=
  "umst/umst-chem/src/impure_pure_adjunction.rs".

Lemma free_purification_refuse :
  impureComponentMorphismConservationFraming <>
  freePurificationFraming /\
  impurePureAdjunctionAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem impure_morphism_not_free_purification :
  impureComponentMorphismConservationFraming <>
  freePurificationFraming /\
  impurePureAdjunctionAuthority =
  "umst/umst-chem/src/impure_pure_adjunction.rs" /\
  impureComponentMorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_impure_morphism_scaffold".

Lemma tp_float_pin_refuse :
  impureComponentMorphismConservationFraming <>
  tpFloatPinFraming /\
  ore_constituent_morphism_channel_tag = "ore_constituent_morphism".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  impureComponentMorphismConservationFraming <>
  tpFloatPinFraming /\
  second_law_gmin_channel_tag = "second_law_presentation" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Impure-component-morphism **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition icm_conservation_coherence_scaffold : bool :=
  icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_proved false false) &&
  negb (icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_unwired true false)) &&
  negb (icm_conservation_verdict_ok
    (evaluate_impure_component_morphism_conservation_close
       impure_component_morphism_conservation_proved false true)).

Lemma icm_conservation_coherence_scaffold_true :
  icm_conservation_coherence_scaffold = true.
Proof.
  unfold icm_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem icm_conservation_coherence_scaffold_theorem :
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_proved false false =
    icm_verdict_named_ok /\
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_unwired true false =
    icm_verdict_green_invent_refuse /\
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_proved false true =
    icm_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition icm_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition icm_conservation_knowing_fiber_ok : bool :=
  icm_conservation_fiber_ok fiber_quantum_knowing.

Definition icm_conservation_meso_acting_ok : bool :=
  icm_conservation_fiber_ok fiber_meso_acting.

Lemma icm_conservation_knowing_fiber_ok_true :
  icm_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma icm_conservation_meso_acting_not_ok :
  icm_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem icm_conservation_routes_knowing_not_meso :
  icm_conservation_knowing_fiber_ok = true /\
  icm_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply icm_conservation_knowing_fiber_ok_true.
  - apply icm_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  icm_conservation_knowing_fiber_ok &&
  negb icm_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, icm_conservation_knowing_fiber_ok,
    icm_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-8 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem impure_component_morphism_conservation_fixture_scaffold :
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false false =
    icm_verdict_named_ok /\
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismEmptyWitness
    impureComponentMorphismClaimBarAbsent false false false =
    icm_verdict_trivial_refuse /\
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent true false false =
    icm_verdict_xor_refuse /\
  evaluate_impure_component_morphism_bundle
    impure_component_morphism_conservation_unwired
    impureComponentMorphismFe26Witness
    impureComponentMorphismClaimBarAbsent false false true =
    icm_verdict_proved_without_bar_refuse /\
  evaluate_impure_component_morphism_conservation_close
    impure_component_morphism_conservation_unwired false false =
    icm_verdict_unwired_ok /\
  icm_conservation_knowing_fiber_ok = true /\
  icm_conservation_meso_acting_ok = false /\
  impureComponentMorphismConservationProved = false /\
  icmProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — impure morphism)     *)
(* ------------------------------------------------------------------ *)

Definition chemL0ImpureComponentMorphismAuthority : string :=
  "umst/umst-chem/src/impure_component_morphism.rs".

Definition chemL0ImpureComponentMorphismTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs".

Definition oreAssemblageAuthority : string :=
  "umst/umst-chem/src/ore_assemblage.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0Ore02CellId : string := "CHEM-L0-ORE-02".

Definition impureComponentMorphismConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-IMPURE-COMPONENT-MORPHISM-CONSERVATION".

Definition impureComponentMorphismConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-IMPURE-COMPONENT-MORPHISM-CONSERVATION ImpureComponentMorphismConservationModality Unwired Assumed Proved Surrogate four-step lattice impureComponentMorphismConservationProved false evaluateImpureComponentMorphismBundle evaluateImpureComponentMorphismConservation named class 8 impure_component_morphism Fe Z=26 ore constituent morphism second law G-min presentation concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel impure morphism axiom refuse species id smuggle refuse extra element id Z=119 refuse free purification CAT-03 refuse impure morphism ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma impure_component_morphism_conservation_cell_id :
  impureComponentMorphismConservationCellId =
  "CHEM-FORMAL-Q-COQ-IMPURE-COMPONENT-MORPHISM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma impure_component_morphism_conservation_cites_l0_table :
  chemL0ImpureComponentMorphismTableAuthority <> "".
Proof. discriminate. Qed.

Lemma impure_component_morphism_conservation_authority_path :
  impureComponentMorphismConservationAuthority =
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs".
Proof. reflexivity. Qed.

Lemma impure_component_morphism_conservation_cites_l0_ore02 :
  chemL0ImpureComponentMorphismAuthority <> "".
Proof. discriminate. Qed.

Lemma impure_component_morphism_conservation_cites_marker :
  icmConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma impure_component_morphism_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma impure_component_morphism_conservation_cites_ore02_cell :
  chemL0Ore02CellId = "CHEM-L0-ORE-02".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma impure_component_morphism_not_26th_axiom :
  impureComponentMorphismConservationFraming <> parallelImpureMorphismAxiomTag.
Proof. discriminate. Qed.

Lemma impure_component_morphism_second_law_conservation_framing :
  impureComponentMorphismConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma impure_component_morphism_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma impure_component_morphism_conservation_modality_unwired :
  impureComponentMorphismConservationModalityCurrent =
  impure_component_morphism_conservation_unwired.
Proof. reflexivity. Qed.

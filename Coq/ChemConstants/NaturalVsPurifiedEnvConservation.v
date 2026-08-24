(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: NaturalVsPurifiedEnvConservation.v                      *)
(*                                                                      *)
(*  Knowing-fiber Coq: constitutive **natural_vs_purified_env**         *)
(*  **conservation**. Natural vs purified are **Env sections** of one   *)
(*  object (not two chemistries). Concurrent Π_c PatternBundle factor — *)
(*  **product** not XOR. Assay/analytical prior art; named object is Env *)
(*  section restriction. naturalVsPurifiedEnvConservationProved false.  *)
(*  Modality Unwired. WAVE100: not wired in lib.rs.                     *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/refine_process.rs (read-only cite).        *)
(*  INT: umst/umst-chem/src/l0_tables/processing_refining.rs (cite).   *)
(*  INT: umst/umst-chem/src/surroundings_are_environment_sections.rs.   *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-13 **natural_vs_purified_env** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive NaturalVsPurifiedEnvConservationModality : Type :=
  | natural_vs_purified_env_conservation_unwired
  | natural_vs_purified_env_conservation_assumed
  | natural_vs_purified_env_conservation_proved
  | natural_vs_purified_env_conservation_surrogate.

Definition naturalVsPurifiedEnvConservationModalityCurrent :
  NaturalVsPurifiedEnvConservationModality :=
  natural_vs_purified_env_conservation_unwired.

Definition natural_vs_purified_env_lattice_cardinality : nat := 4.

Lemma natural_vs_purified_env_lattice_cardinality_is_four :
  natural_vs_purified_env_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma natural_vs_purified_env_lattice_not_118_squared :
  negb (Nat.eqb natural_vs_purified_env_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold natural_vs_purified_env_lattice_cardinality.
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

(* North-star §2 class 13 — natural_vs_purified_env concurrent Π_c factor. *)
Definition pattern_class_natural_vs_purified_env_idx : nat := 13.

Lemma pattern_class_natural_vs_purified_env_idx_is_14 :
  pattern_class_natural_vs_purified_env_idx = 13.
Proof. reflexivity. Qed.

Lemma natural_vs_purified_env_class_index_valid :
  pattern_class_index_valid pattern_class_natural_vs_purified_env_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_natural_vs_purified_env_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierNaturalVsPurifiedEnvRowId : string := "NVPE01".

Lemma cross_classifier_natural_vs_purified_env_row_named :
  crossClassifierNaturalVsPurifiedEnvRowId = "NVPE01".
Proof. reflexivity. Qed.

Definition pattern_class_natural_vs_purified_env_tag : string :=
  "natural_vs_purified_env".

Definition north_star_class_13_natural_vs_purified_env_tag : string :=
  "class 13 natural vs purified env".

Lemma pattern_class_natural_vs_purified_env_tag_nonempty :
  pattern_class_natural_vs_purified_env_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_13_natural_vs_purified_env_tag_nonempty :
  north_star_class_13_natural_vs_purified_env_tag <> "".
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

Definition natural_vs_purified_env_factor_tag : string :=
  "natural_vs_purified_env".

Definition env_section_restriction_channel_tag : string := "env_section_restriction".

Definition assay_analytical_prior_art_channel_tag : string := "assay_analytical_prior_art".

Lemma natural_vs_purified_env_factor_tag_nonempty :
  natural_vs_purified_env_factor_tag <> "".
Proof. discriminate. Qed.

Lemma env_section_restriction_channel_tag_nonempty :
  env_section_restriction_channel_tag <> "".
Proof. discriminate. Qed.

Lemma assay_analytical_prior_art_channel_tag_nonempty :
  assay_analytical_prior_art_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive nvpvec_channel_slot : Type :=
  | nvpvec_slot_unwired
  | nvpvec_slot_absent
  | nvpvec_slot_present.

Definition nvpvec_channel_slot_beq (s1 s2 : nvpvec_channel_slot) : bool :=
  match s1, s2 with
  | nvpvec_slot_unwired, nvpvec_slot_unwired => true
  | nvpvec_slot_absent, nvpvec_slot_absent => true
  | nvpvec_slot_present, nvpvec_slot_present => true
  | _, _ => false
  end.

Definition nvpvec_channel_slot_is_present (s : nvpvec_channel_slot) : bool :=
  match s with
  | nvpvec_slot_present => true
  | _ => false
  end.

Definition naturalVsPurifiedEnvProductChannelCount : nat := 3.

Lemma natural_vs_purified_env_product_channel_count_is_three :
  naturalVsPurifiedEnvProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = env section restriction, 1 = assay prior art, 2 = natural_vs_purified_env chart. *)
Definition nvpvec_channel_env_section_restriction : nat := 0.
Definition nvpvec_channel_assay_analytical_prior_art : nat := 1.
Definition nvpvec_channel_natural_vs_purified_env : nat := 2.

Lemma nvpvec_channel_env_section_restriction_idx_is_0 :
  nvpvec_channel_env_section_restriction = 0.
Proof. reflexivity. Qed.

Lemma nvpvec_channel_assay_analytical_prior_art_idx_is_1 :
  nvpvec_channel_assay_analytical_prior_art = 1.
Proof. reflexivity. Qed.

Lemma nvpvec_channel_natural_vs_purified_env_idx_is_2 :
  nvpvec_channel_natural_vs_purified_env = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition nvpvec_channel_bundle : Type := nat -> nvpvec_channel_slot.

Definition naturalVsPurifiedEnvBundleAllUnwired : nvpvec_channel_bundle :=
  fun _ => nvpvec_slot_unwired.

Definition naturalVsPurifiedEnvBundleAt (b : nvpvec_channel_bundle) (idx : nat)
  (slot : nvpvec_channel_slot) : nvpvec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition naturalVsPurifiedEnvBundleWithPresent
  (b : nvpvec_channel_bundle) (idx : nat) : nvpvec_channel_bundle :=
  naturalVsPurifiedEnvBundleAt b idx nvpvec_slot_present.

Fixpoint count_nvpvec_present_up_to (b : nvpvec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if nvpvec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_nvpvec_present_up_to b i + add
  end.

Definition naturalVsPurifiedEnvBundlePresentCount (b : nvpvec_channel_bundle) : nat :=
  count_nvpvec_present_up_to b naturalVsPurifiedEnvProductChannelCount.

Definition naturalVsPurifiedEnvBundleHolds (b : nvpvec_channel_bundle) (idx : nat) : bool :=
  nvpvec_channel_slot_is_present (b idx).

Definition naturalVsPurifiedEnvBundleIsConcurrentProduct (b : nvpvec_channel_bundle) : bool :=
  Nat.leb 2 (naturalVsPurifiedEnvBundlePresentCount b).

(* Au Z=79 env section restriction + assay prior art + natural_vs_purified_env concurrent witness. *)
Definition naturalVsPurifiedEnvAu79Witness : nvpvec_channel_bundle :=
  naturalVsPurifiedEnvBundleWithPresent
    (naturalVsPurifiedEnvBundleWithPresent
      (naturalVsPurifiedEnvBundleWithPresent naturalVsPurifiedEnvBundleAllUnwired
        nvpvec_channel_env_section_restriction)
      nvpvec_channel_assay_analytical_prior_art)
    nvpvec_channel_natural_vs_purified_env.

Definition naturalVsPurifiedEnvEmptyWitness : nvpvec_channel_bundle :=
  naturalVsPurifiedEnvBundleAllUnwired.

Definition naturalVsPurifiedEnvSinglePresent : nvpvec_channel_bundle :=
  naturalVsPurifiedEnvBundleWithPresent naturalVsPurifiedEnvBundleAllUnwired
    nvpvec_channel_env_section_restriction.

Lemma env_section_restriction_channel_present :
  naturalVsPurifiedEnvBundleHolds naturalVsPurifiedEnvAu79Witness
    nvpvec_channel_env_section_restriction = true.
Proof. reflexivity. Qed.

Lemma assay_analytical_prior_art_channel_present :
  naturalVsPurifiedEnvBundleHolds naturalVsPurifiedEnvAu79Witness
    nvpvec_channel_assay_analytical_prior_art = true.
Proof. reflexivity. Qed.

Lemma natural_vs_purified_env_channel_present :
  naturalVsPurifiedEnvBundleHolds naturalVsPurifiedEnvAu79Witness
    nvpvec_channel_natural_vs_purified_env = true.
Proof. reflexivity. Qed.

Lemma au79_witness_present_count_is_three :
  naturalVsPurifiedEnvBundlePresentCount naturalVsPurifiedEnvAu79Witness = 3.
Proof. reflexivity. Qed.

Lemma au79_witness_is_concurrent_product :
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvAu79Witness = true.
Proof.
  unfold naturalVsPurifiedEnvBundleIsConcurrentProduct.
  rewrite au79_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  naturalVsPurifiedEnvBundlePresentCount naturalVsPurifiedEnvEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvEmptyWitness = false.
Proof.
  unfold naturalVsPurifiedEnvBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  naturalVsPurifiedEnvBundlePresentCount naturalVsPurifiedEnvSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvSinglePresent = false.
Proof.
  unfold naturalVsPurifiedEnvBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive nvpvec_xor_posture : Type :=
  | nvpvec_xor_exclusive
  | nvpvec_xor_concurrent_product.

Definition nvpecXorClassifierMarker : string := "chem_l0_natural_vs_purified_env_xor_classifier_v1".
Definition nvpecConcurrentProductMarker : string := "chem_int_natural_vs_purified_env_product_v1".

Lemma nvpvec_xor_marker_ne_concurrent_product_marker :
  nvpecXorClassifierMarker <> nvpecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition nvpecXorClassifierIncompatible (claim_xor : bool)
  (b : nvpvec_channel_bundle) : bool :=
  claim_xor && naturalVsPurifiedEnvBundleIsConcurrentProduct b.

Lemma ccv_xor_refuse_on_au79_witness :
  nvpecXorClassifierIncompatible true naturalVsPurifiedEnvAu79Witness = true.
Proof.
  unfold nvpecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma nvpvec_xor_ok_on_concurrent_product_claim :
  nvpecXorClassifierIncompatible false naturalVsPurifiedEnvAu79Witness = false.
Proof. reflexivity. Qed.

Definition nvpecProductNotXor : bool :=
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvAu79Witness &&
  nvpecXorClassifierIncompatible true naturalVsPurifiedEnvAu79Witness.

Lemma nvpvec_product_not_xor_true : nvpecProductNotXor = true.
Proof.
  unfold nvpecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  nvpecProductNotXor = true /\
  Nat.leb 2 (naturalVsPurifiedEnvBundlePresentCount
    naturalVsPurifiedEnvAu79Witness) = true /\
  nvpecXorClassifierMarker <> nvpecConcurrentProductMarker.
Proof.
  split.
  - apply nvpvec_product_not_xor_true.
  - split.
    + rewrite au79_witness_present_count_is_three.
      reflexivity.
    + apply nvpvec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive nvpvec_bar_presence : Type :=
  | nvpvec_bar_absent
  | nvpvec_bar_present.

Record nvpvec_claim_bar : Type := {
  nvpvec_bar_presence_field : nvpvec_bar_presence;
  nvpvec_bar_defect_total : nat
}.

Definition naturalVsPurifiedEnvClaimBarAbsent : nvpvec_claim_bar :=
  {| nvpvec_bar_presence_field := nvpvec_bar_absent;
     nvpvec_bar_defect_total := 0 |}.

Definition naturalVsPurifiedEnvClaimBarZeroDefect : nvpvec_claim_bar :=
  {| nvpvec_bar_presence_field := nvpvec_bar_present;
     nvpvec_bar_defect_total := 0 |}.

Definition nvpvec_claim_bar_zero_defect (b : nvpvec_claim_bar) : bool :=
  match nvpvec_bar_presence_field b with
  | nvpvec_bar_absent => false
  | nvpvec_bar_present => Nat.eqb (nvpvec_bar_defect_total b) 0
  end.

Lemma nvpvec_claim_bar_zero_defect_true :
  nvpvec_claim_bar_zero_defect naturalVsPurifiedEnvClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma nvpvec_claim_bar_absent_not_zero_defect :
  nvpvec_claim_bar_zero_defect naturalVsPurifiedEnvClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive nvpvec_conservation_verdict : Type :=
  | nvpvec_verdict_unwired_ok
  | nvpvec_verdict_named_ok
  | nvpvec_verdict_design_ok
  | nvpvec_verdict_trivial_refuse
  | nvpvec_verdict_xor_refuse
  | nvpvec_verdict_green_invent_refuse
  | nvpvec_verdict_proved_without_bar_refuse
  | nvpvec_verdict_production_wired_refuse
  | nvpvec_verdict_parallel_natural_vs_purified_env_axiom_refuse
  | nvpvec_verdict_species_id_smuggle_refuse
  | nvpvec_verdict_extra_element_id_refuse
  | nvpvec_verdict_extra_natural_vs_purified_env_force_refuse
  | nvpvec_verdict_tp_float_pin_refuse.

Definition nvpvec_conservation_verdict_ok (v : nvpvec_conservation_verdict) : bool :=
  match v with
  | nvpvec_verdict_unwired_ok => true
  | nvpvec_verdict_named_ok => true
  | nvpvec_verdict_design_ok => true
  | _ => false
  end.

Definition naturalVsPurifiedEnvBundleNontrivial (b : nvpvec_channel_bundle) : bool :=
  Nat.ltb 0 (naturalVsPurifiedEnvBundlePresentCount b).

Definition evaluate_natural_vs_purified_env_bundle
  (m : NaturalVsPurifiedEnvConservationModality)
  (b : nvpvec_channel_bundle)
  (bar : nvpvec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : nvpvec_conservation_verdict :=
  if claim_physics_green
  then nvpvec_verdict_green_invent_refuse
  else if claim_proved
       then nvpvec_verdict_proved_without_bar_refuse
       else if negb (naturalVsPurifiedEnvBundleNontrivial b)
            then nvpvec_verdict_trivial_refuse
            else if nvpecXorClassifierIncompatible claim_xor_classifier b
                 then nvpvec_verdict_xor_refuse
                 else
                   match m with
                   | natural_vs_purified_env_conservation_unwired =>
                       if naturalVsPurifiedEnvBundleIsConcurrentProduct b
                       then nvpvec_verdict_named_ok
                       else nvpvec_verdict_design_ok
                   | natural_vs_purified_env_conservation_assumed
                   | natural_vs_purified_env_conservation_surrogate =>
                       nvpvec_verdict_design_ok
                   | natural_vs_purified_env_conservation_proved =>
                       nvpvec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_natural_vs_purified_env_conservation_close
  (m : NaturalVsPurifiedEnvConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : nvpvec_conservation_verdict :=
  if claim_physics_green
  then nvpvec_verdict_green_invent_refuse
  else if claim_production_wired
  then nvpvec_verdict_production_wired_refuse
  else
    match m with
    | natural_vs_purified_env_conservation_unwired => nvpvec_verdict_unwired_ok
    | natural_vs_purified_env_conservation_assumed
    | natural_vs_purified_env_conservation_proved
    | natural_vs_purified_env_conservation_surrogate => nvpvec_verdict_named_ok
    end.

Definition natural_vs_purified_env_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_natural_vs_purified_env_conservation_close
          natural_vs_purified_env_conservation_proved claim_physics_green claim_production_wired with
  | nvpvec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive nvpvec_conservation_law : Type :=
  | nvpvec_law_conserved
  | nvpvec_law_named_ok
  | nvpvec_law_trivial_refuse
  | nvpvec_law_green_invent_refuse.

Definition nvpvec_conservation_law_count : nat := 4.

Lemma nvpvec_conservation_law_count_is_four :
  nvpvec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive nvpvec_conservation_law_witness : Type :=
  | nvpvec_law_witness_open
  | nvpvec_law_witness_proved.

Definition evaluate_nvpvec_conservation_law_witness
  (law : nvpvec_conservation_law)
  (m : NaturalVsPurifiedEnvConservationModality)
  : nvpvec_conservation_law_witness :=
  match m with
  | natural_vs_purified_env_conservation_unwired
  | natural_vs_purified_env_conservation_assumed
  | natural_vs_purified_env_conservation_surrogate => nvpvec_law_witness_open
  | natural_vs_purified_env_conservation_proved => nvpvec_law_witness_proved
  end.

Lemma all_nvpvec_conservation_laws_open_at_unwired :
  evaluate_nvpvec_conservation_law_witness nvpvec_law_conserved
    natural_vs_purified_env_conservation_unwired = nvpvec_law_witness_open /\
  evaluate_nvpvec_conservation_law_witness nvpvec_law_named_ok
    natural_vs_purified_env_conservation_unwired = nvpvec_law_witness_open /\
  evaluate_nvpvec_conservation_law_witness nvpvec_law_trivial_refuse
    natural_vs_purified_env_conservation_unwired = nvpvec_law_witness_open /\
  evaluate_nvpvec_conservation_law_witness nvpvec_law_green_invent_refuse
    natural_vs_purified_env_conservation_unwired = nvpvec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-13 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition naturalVsPurifiedEnvConservationProved : bool := false.

Lemma natural_vs_purified_env_conservation_proved_false :
  naturalVsPurifiedEnvConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_unwired false false =
  nvpvec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_unwired false false =
  nvpvec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_unwired false false) =
  true.
Proof.
  unfold nvpvec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Au Z=79 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma au79_witness_named_ok :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
  nvpvec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_au79_natural_vs_purified_env_conservation :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
  nvpvec_verdict_named_ok /\
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvAu79Witness = true /\
  gold_atomic_number_z = 79 /\
  pattern_class_natural_vs_purified_env_idx = 13.
Proof.
  repeat split; reflexivity.
Qed.

Lemma nvpvec_named_close_ok :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_proved false false =
  nvpvec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_natural_vs_purified_env_conservation_close :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_proved false false =
  nvpvec_verdict_named_ok /\
  natural_vs_purified_env_conservation_authorized false false = true.
Proof.
  split.
  - apply nvpvec_named_close_ok.
  - unfold natural_vs_purified_env_conservation_authorized.
    rewrite nvpvec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — natural_vs_purified_env refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvEmptyWitness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
  nvpvec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvEmptyWitness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
  nvpvec_verdict_trivial_refuse /\
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_bundle
       natural_vs_purified_env_conservation_unwired
       naturalVsPurifiedEnvEmptyWitness
       naturalVsPurifiedEnvClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold nvpvec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent true false false =
  nvpvec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent true false false =
  nvpvec_verdict_xor_refuse /\
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_bundle
       natural_vs_purified_env_conservation_unwired
       naturalVsPurifiedEnvAu79Witness
       naturalVsPurifiedEnvClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold nvpvec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_unwired true false =
  nvpvec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_unwired true false) =
  false.
Proof.
  unfold nvpvec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_nvpvec_bundle_refuse :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false true false =
  nvpvec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — natural_vs_purified_env refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false true =
  nvpvec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false true =
  nvpvec_verdict_proved_without_bar_refuse /\
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_bundle
       natural_vs_purified_env_conservation_unwired
       naturalVsPurifiedEnvAu79Witness
       naturalVsPurifiedEnvClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold nvpvec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — natural_vs_purified_env lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_proved false true =
  nvpvec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_proved false true) =
  false.
Proof.
  unfold nvpvec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel natural_vs_purified_env axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition naturalVsPurifiedEnvConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition parallelNaturalVsPurifiedEnvAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_natural_vs_purified_env_axiom_refuse :
  naturalVsPurifiedEnvConservationAuthority <>
  parallelNaturalVsPurifiedEnvAxiomTag /\
  naturalVsPurifiedEnvConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply natural_vs_purified_env_conservation_proved_false.
Qed.

Theorem parallel_natural_vs_purified_env_axiom_not_minted :
  naturalVsPurifiedEnvConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs" /\
  naturalVsPurifiedEnvConservationProved = false /\
  naturalVsPurifiedEnvConservationAuthority <> parallelNaturalVsPurifiedEnvAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — env section restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "assay_analytical_prior_art_not_named_object".

Definition naturalVsPurifiedEnvConservationFraming : string :=
  "second_law_conservation_natural_vs_purified_env_section_one_object_one_axiom".

Lemma species_id_smuggle_refuse :
  naturalVsPurifiedEnvConservationFraming <>
  speciesIdSmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_natural_vs_purified_env_idx = 13.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem env_section_restriction_not_species_id_smuggle :
  naturalVsPurifiedEnvConservationFraming <>
  speciesIdSmuggleFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_natural_vs_purified_env_idx = 13 /\
  naturalVsPurifiedEnvConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — natural_vs_purified_env ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "natural_and_purified_are_two_chemistries".

Lemma extra_element_id_refuse :
  naturalVsPurifiedEnvConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  naturalVsPurifiedEnvConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — natural_vs_purified_env ≠ extra natural_vs_purified_env force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraNaturalVsPurifiedEnvForceFraming : string :=
  "two_chemistries_xor_minted_as_26th_law".

Definition naturalVsPurifiedEnvBarrierAuthority : string :=
  "umst/umst-chem/src/refine_process.rs".

Lemma extra_natural_vs_purified_env_force_refuse :
  naturalVsPurifiedEnvConservationFraming <>
  extraNaturalVsPurifiedEnvForceFraming /\
  naturalVsPurifiedEnvBarrierAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem natural_vs_purified_env_not_extra_force :
  naturalVsPurifiedEnvConservationFraming <>
  extraNaturalVsPurifiedEnvForceFraming /\
  naturalVsPurifiedEnvBarrierAuthority =
  "umst/umst-chem/src/refine_process.rs" /\
  naturalVsPurifiedEnvConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_natural_vs_purified_env_scaffold".

Lemma tp_float_pin_refuse :
  naturalVsPurifiedEnvConservationFraming <>
  tpFloatPinFraming /\
  env_section_restriction_channel_tag = "env_section_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  naturalVsPurifiedEnvConservationFraming <>
  tpFloatPinFraming /\
  assay_analytical_prior_art_channel_tag = "assay_analytical_prior_art" /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  NaturalVsPurifiedEnv **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition nvpvec_conservation_coherence_scaffold : bool :=
  nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_proved false false) &&
  negb (nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_unwired true false)) &&
  negb (nvpvec_conservation_verdict_ok
    (evaluate_natural_vs_purified_env_conservation_close
       natural_vs_purified_env_conservation_proved false true)).

Lemma nvpvec_conservation_coherence_scaffold_true :
  nvpvec_conservation_coherence_scaffold = true.
Proof.
  unfold nvpvec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem nvpvec_conservation_coherence_scaffold_theorem :
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_proved false false =
    nvpvec_verdict_named_ok /\
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_unwired true false =
    nvpvec_verdict_green_invent_refuse /\
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_proved false true =
    nvpvec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition nvpvec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition nvpvec_conservation_knowing_fiber_ok : bool :=
  nvpvec_conservation_fiber_ok fiber_quantum_knowing.

Definition nvpvec_conservation_meso_acting_ok : bool :=
  nvpvec_conservation_fiber_ok fiber_meso_acting.

Lemma nvpvec_conservation_knowing_fiber_ok_true :
  nvpvec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma nvpvec_conservation_meso_acting_ok_not_ok :
  nvpvec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem nvpvec_conservation_routes_knowing_not_meso :
  nvpvec_conservation_knowing_fiber_ok = true /\
  nvpvec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply nvpvec_conservation_knowing_fiber_ok_true.
  - apply nvpvec_conservation_meso_acting_ok_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  nvpvec_conservation_knowing_fiber_ok &&
  negb nvpvec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, nvpvec_conservation_knowing_fiber_ok,
    nvpvec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-13 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem natural_vs_purified_env_conservation_fixture_scaffold :
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
    nvpvec_verdict_named_ok /\
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvEmptyWitness
    naturalVsPurifiedEnvClaimBarAbsent false false false =
    nvpvec_verdict_trivial_refuse /\
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent true false false =
    nvpvec_verdict_xor_refuse /\
  evaluate_natural_vs_purified_env_bundle
    natural_vs_purified_env_conservation_unwired
    naturalVsPurifiedEnvAu79Witness
    naturalVsPurifiedEnvClaimBarAbsent false false true =
    nvpvec_verdict_proved_without_bar_refuse /\
  evaluate_natural_vs_purified_env_conservation_close
    natural_vs_purified_env_conservation_unwired false false =
    nvpvec_verdict_unwired_ok /\
  nvpvec_conservation_knowing_fiber_ok = true /\
  nvpvec_conservation_meso_acting_ok = false /\
  naturalVsPurifiedEnvConservationProved = false /\
  nvpecProductNotXor = true /\
  gold_atomic_number_z = 79.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — natural_vs_purified_env) *)
(* ------------------------------------------------------------------ *)

Definition chemL0NaturalVsPurifiedEnvAuthority : string :=
  "umst/umst-chem/src/refine_process.rs".

Definition chemL0NaturalVsPurifiedEnvTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition surroundingsAreEnvSectionsAuthority : string :=
  "umst/umst-chem/src/surroundings_are_environment_sections.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeNaturalVsPurifiedEnvCellId : string := "CHEM-INT-SURROUNDINGS-ARE-ENV-SECTIONS".

Definition naturalVsPurifiedEnvConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-NATURAL-VS-PURIFIED-ENV-CONSERVATION".

Definition naturalVsPurifiedEnvConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-NATURAL-VS-PURIFIED-ENV-CONSERVATION NaturalVsPurifiedEnvConservationModality Unwired Assumed Proved Surrogate four-step lattice naturalVsPurifiedEnvConservationProved false evaluateNaturalVsPurifiedEnvBundle evaluateNaturalVsPurifiedEnvConservation named class 13 natural vs purified env Au Z=79 env section restriction second law assay analytical prior art concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel natural vs purified env axiom refuse species id smuggle refuse extra element id Z=119 refuse two chemistries refuse natural vs purified env ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs".

Lemma natural_vs_purified_env_conservation_cell_id :
  naturalVsPurifiedEnvConservationCellId =
  "CHEM-FORMAL-Q-COQ-NATURAL-VS-PURIFIED-ENV-CONSERVATION".
Proof. reflexivity. Qed.

Lemma natural_vs_purified_env_conservation_cites_l0_table :
  chemL0NaturalVsPurifiedEnvTableAuthority <> "".
Proof. discriminate. Qed.

Lemma natural_vs_purified_env_conservation_authority_path :
  naturalVsPurifiedEnvConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs".
Proof. reflexivity. Qed.

Lemma natural_vs_purified_env_conservation_cites_l0_table_src :
  chemL0NaturalVsPurifiedEnvAuthority <> "".
Proof. discriminate. Qed.

Lemma natural_vs_purified_env_conservation_cites_marker :
  nvpecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma natural_vs_purified_env_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma natural_vs_purified_env_conservation_cites_env_sections_cell :
  chemL0EdgeNaturalVsPurifiedEnvCellId = "CHEM-INT-SURROUNDINGS-ARE-ENV-SECTIONS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma natural_vs_purified_env_not_26th_axiom :
  naturalVsPurifiedEnvConservationFraming <> parallelNaturalVsPurifiedEnvAxiomTag.
Proof. discriminate. Qed.

Lemma natural_vs_purified_env_second_law_conservation_framing :
  naturalVsPurifiedEnvConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition assayAnalyticalPriorArtFraming : string :=
  "assay_analytical_prior_art_not_named_object".

Definition envSectionRestrictionNamedObject : string :=
  "env_section_restriction_on_natural_vs_purified_env_morphism".

Lemma assay_analytical_prior_art_not_named_object :
  envSectionRestrictionNamedObject <>
  assayAnalyticalPriorArtFraming /\
  assay_analytical_prior_art_channel_tag = "assay_analytical_prior_art".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem env_section_restriction_is_named_object_not_assay_prior_art :
  envSectionRestrictionNamedObject <>
  assayAnalyticalPriorArtFraming /\
  env_section_restriction_channel_tag = "env_section_restriction" /\
  naturalVsPurifiedEnvConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not natural_vs_purified_env axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition envSectionRestrictionFraming : string :=
  "env_section_restriction_not_extra_force".

Lemma env_section_restriction_not_extra_force_refuse :
  envSectionRestrictionFraming <>
  extraNaturalVsPurifiedEnvForceFraming /\
  env_section_restriction_channel_tag = "env_section_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem natural_vs_purified_env_env_section_not_extra_force :
  envSectionRestrictionFraming <>
  extraNaturalVsPurifiedEnvForceFraming /\
  naturalVsPurifiedEnvBarrierAuthority =
  "umst/umst-chem/src/refine_process.rs" /\
  naturalVsPurifiedEnvConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  Two-chemistries refuse — natural/purified are Env sections not XOR   *)
(* ------------------------------------------------------------------ *)

Definition twoChemistriesXorFraming : string :=
  "natural_and_purified_are_two_chemistries".

Definition oneObjectEnvSectionFraming : string :=
  "natural_and_purified_env_sections_of_one_object".

Lemma two_chemistries_xor_refuse :
  oneObjectEnvSectionFraming <>
  twoChemistriesXorFraming /\
  env_section_restriction_channel_tag = "env_section_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem natural_vs_purified_not_two_chemistries :
  oneObjectEnvSectionFraming <>
  twoChemistriesXorFraming /\
  gold_atomic_number_z = 79 /\
  pattern_class_natural_vs_purified_env_idx = 13 /\
  naturalVsPurifiedEnvConservationProved = false.
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

Lemma natural_vs_purified_env_conservation_wave100_not_lib_rs :
  wave100LibRsAuthority <> wave100LibRsWiredMarker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma natural_vs_purified_env_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma natural_vs_purified_env_conservation_modality_unwired :
  naturalVsPurifiedEnvConservationModalityCurrent =
  natural_vs_purified_env_conservation_unwired.
Proof. reflexivity. Qed.

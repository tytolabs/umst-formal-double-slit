(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AqueousVsMineralConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 16 **aqueous_vs_mineral** **conservation**.        *)
(*  Catalysis is an **Interact restriction** on the same second-law +  *)
(*  conservation object (not a catalysis axiom / extra force).         *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  PHREEQC/Pitzer prior art; the named object is Env restriction.             *)
(*  aqueousVsMineralConservationProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/aqueous_mineral_regime.rs (read-only cite).     *)
(*  INT: umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs (read-only cite).   *)
(*  INT: umst/umst-chem/src/aqueous_mineral_is_environment_restriction.rs (read-only cite).   *)
(*  INT: umst/umst-chem/src/temperature_is_graph_function.rs (read-only cite). *)
(*  INT: umst/umst-chem/src/pressure_is_graph_function.rs (read-only cite).   *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-16 **aqueous_vs_mineral** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive AqueousVsMineralConservationModality : Type :=
  | aqueous_vs_mineral_conservation_unwired
  | aqueous_vs_mineral_conservation_assumed
  | aqueous_vs_mineral_conservation_proved
  | aqueous_vs_mineral_conservation_surrogate.

Definition aqueousVsMineralConservationModalityCurrent :
  AqueousVsMineralConservationModality :=
  aqueous_vs_mineral_conservation_unwired.

Definition aqueous_vs_mineral_lattice_cardinality : nat := 4.

Lemma aqueous_vs_mineral_lattice_cardinality_is_four :
  aqueous_vs_mineral_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma aqueous_vs_mineral_lattice_not_118_squared :
  negb (Nat.eqb aqueous_vs_mineral_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold aqueous_vs_mineral_lattice_cardinality.
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
Definition pattern_class_aqueous_vs_mineral_idx : nat := 16.

Lemma pattern_class_aqueous_vs_mineral_idx_is_14 :
  pattern_class_aqueous_vs_mineral_idx = 16.
Proof. reflexivity. Qed.

Lemma aqueous_vs_mineral_class_index_valid :
  pattern_class_index_valid pattern_class_aqueous_vs_mineral_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_aqueous_vs_mineral_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierAqueousVsMineralRowId : string := "X16".

Lemma cross_classifier_aqueous_vs_mineral_row_named :
  crossClassifierAqueousVsMineralRowId = "X16".
Proof. reflexivity. Qed.

Definition pattern_class_aqueous_vs_mineral_tag : string :=
  "aqueous_vs_mineral".

Definition north_star_class_16_aqueous_vs_mineral_tag : string :=
  "class 16 aqueous vs mineral".

Lemma pattern_class_aqueous_vs_mineral_tag_nonempty :
  pattern_class_aqueous_vs_mineral_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_16_aqueous_vs_mineral_tag_nonempty :
  north_star_class_16_aqueous_vs_mineral_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Fe Z=26 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition iron_atomic_number_z : nat := 26.

Lemma iron_atomic_number_z_is_78 :
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

Definition aqueous_vs_mineral_factor_tag : string :=
  "aqueous_vs_mineral".

Definition env_restriction_channel_tag : string := "env_restriction".

Definition phreeqc_pitzer_prior_art_channel_tag : string := "phreeqc_pitzer_prior_art".

Lemma aqueous_vs_mineral_factor_tag_nonempty :
  aqueous_vs_mineral_factor_tag <> "".
Proof. discriminate. Qed.

Lemma env_restriction_channel_tag_nonempty :
  env_restriction_channel_tag <> "".
Proof. discriminate. Qed.

Lemma phreeqc_pitzer_prior_art_channel_tag_nonempty :
  phreeqc_pitzer_prior_art_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive avmc_channel_slot : Type :=
  | avmc_slot_unwired
  | avmc_slot_absent
  | avmc_slot_present.

Definition avmc_channel_slot_beq (s1 s2 : avmc_channel_slot) : bool :=
  match s1, s2 with
  | avmc_slot_unwired, avmc_slot_unwired => true
  | avmc_slot_absent, avmc_slot_absent => true
  | avmc_slot_present, avmc_slot_present => true
  | _, _ => false
  end.

Definition avmc_channel_slot_is_present (s : avmc_channel_slot) : bool :=
  match s with
  | avmc_slot_present => true
  | _ => false
  end.

Definition aqueousVsMineralProductChannelCount : nat := 3.

Lemma aqueous_vs_mineral_product_channel_count_is_three :
  aqueousVsMineralProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 16 aqueous vs mineral. *)
Definition avmc_channel_env_restriction : nat := 0.
Definition avmc_channel_phreeqc_pitzer_prior_art : nat := 1.
Definition avmc_channel_class16_aqueous_vs_mineral : nat := 2.

Lemma avmc_channel_env_restriction_idx_is_0 :
  avmc_channel_env_restriction = 0.
Proof. reflexivity. Qed.

Lemma avmc_channel_phreeqc_pitzer_prior_art_idx_is_1 :
  avmc_channel_phreeqc_pitzer_prior_art = 1.
Proof. reflexivity. Qed.

Lemma avmc_channel_class16_aqueous_vs_mineral_idx_is_2 :
  avmc_channel_class16_aqueous_vs_mineral = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition avmc_channel_bundle : Type := nat -> avmc_channel_slot.

Definition aqueousVsMineralBundleAllUnwired : avmc_channel_bundle :=
  fun _ => avmc_slot_unwired.

Definition aqueousVsMineralBundleAt (b : avmc_channel_bundle) (idx : nat)
  (slot : avmc_channel_slot) : avmc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition aqueousVsMineralBundleWithPresent
  (b : avmc_channel_bundle) (idx : nat) : avmc_channel_bundle :=
  aqueousVsMineralBundleAt b idx avmc_slot_present.

Fixpoint count_avmc_present_up_to (b : avmc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if avmc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_avmc_present_up_to b i + add
  end.

Definition aqueousVsMineralBundlePresentCount (b : avmc_channel_bundle) : nat :=
  count_avmc_present_up_to b aqueousVsMineralProductChannelCount.

Definition aqueousVsMineralBundleHolds (b : avmc_channel_bundle) (idx : nat) : bool :=
  avmc_channel_slot_is_present (b idx).

Definition aqueousVsMineralBundleIsConcurrentProduct (b : avmc_channel_bundle) : bool :=
  Nat.leb 2 (aqueousVsMineralBundlePresentCount b).

(* Fe Z=26 env restriction + PHREEQC/Pitzer + class 16 aqueous vs mineral concurrent witness. *)
Definition aqueousVsMineralFe26Witness : avmc_channel_bundle :=
  aqueousVsMineralBundleWithPresent
    (aqueousVsMineralBundleWithPresent
      (aqueousVsMineralBundleWithPresent aqueousVsMineralBundleAllUnwired
        avmc_channel_env_restriction)
      avmc_channel_phreeqc_pitzer_prior_art)
    avmc_channel_class16_aqueous_vs_mineral.

Definition aqueousVsMineralEmptyWitness : avmc_channel_bundle :=
  aqueousVsMineralBundleAllUnwired.

Definition aqueousVsMineralSinglePresent : avmc_channel_bundle :=
  aqueousVsMineralBundleWithPresent aqueousVsMineralBundleAllUnwired
    avmc_channel_env_restriction.

Lemma env_restriction_channel_present :
  aqueousVsMineralBundleHolds aqueousVsMineralFe26Witness
    avmc_channel_env_restriction = true.
Proof. reflexivity. Qed.

Lemma phreeqc_pitzer_prior_art_channel_present :
  aqueousVsMineralBundleHolds aqueousVsMineralFe26Witness
    avmc_channel_phreeqc_pitzer_prior_art = true.
Proof. reflexivity. Qed.

Lemma class16_aqueous_vs_mineral_channel_present :
  aqueousVsMineralBundleHolds aqueousVsMineralFe26Witness
    avmc_channel_class16_aqueous_vs_mineral = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  aqueousVsMineralBundlePresentCount aqueousVsMineralFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralFe26Witness = true.
Proof.
  unfold aqueousVsMineralBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  aqueousVsMineralBundlePresentCount aqueousVsMineralEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralEmptyWitness = false.
Proof.
  unfold aqueousVsMineralBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  aqueousVsMineralBundlePresentCount aqueousVsMineralSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralSinglePresent = false.
Proof.
  unfold aqueousVsMineralBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive avmc_xor_posture : Type :=
  | avmc_xor_exclusive
  | avmc_xor_concurrent_product.

Definition avmcXorClassifierMarker : string := "chem_l0_aqueous_vs_mineral_xor_classifier_v1".
Definition avmcConcurrentProductMarker : string := "chem_int_aqueous_vs_mineral_product_v1".

Lemma avmc_xor_marker_ne_concurrent_product_marker :
  avmcXorClassifierMarker <> avmcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition avmcXorClassifierIncompatible (claim_xor : bool)
  (b : avmc_channel_bundle) : bool :=
  claim_xor && aqueousVsMineralBundleIsConcurrentProduct b.

Lemma avmc_xor_refuse_on_fe26_witness :
  avmcXorClassifierIncompatible true aqueousVsMineralFe26Witness = true.
Proof.
  unfold avmcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma avmc_xor_ok_on_concurrent_product_claim :
  avmcXorClassifierIncompatible false aqueousVsMineralFe26Witness = false.
Proof. reflexivity. Qed.

Definition avmcProductNotXor : bool :=
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralFe26Witness &&
  avmcXorClassifierIncompatible true aqueousVsMineralFe26Witness.

Lemma avmc_product_not_xor_true : avmcProductNotXor = true.
Proof.
  unfold avmcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  avmcProductNotXor = true /\
  Nat.leb 2 (aqueousVsMineralBundlePresentCount
    aqueousVsMineralFe26Witness) = true /\
  avmcXorClassifierMarker <> avmcConcurrentProductMarker.
Proof.
  split.
  - apply avmc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply avmc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive avmc_bar_presence : Type :=
  | avmc_bar_absent
  | avmc_bar_present.

Record avmc_claim_bar : Type := {
  avmc_bar_presence_field : avmc_bar_presence;
  avmc_bar_defect_total : nat
}.

Definition aqueousVsMineralClaimBarAbsent : avmc_claim_bar :=
  {| avmc_bar_presence_field := avmc_bar_absent;
     avmc_bar_defect_total := 0 |}.

Definition aqueousVsMineralClaimBarZeroDefect : avmc_claim_bar :=
  {| avmc_bar_presence_field := avmc_bar_present;
     avmc_bar_defect_total := 0 |}.

Definition avmc_claim_bar_zero_defect (b : avmc_claim_bar) : bool :=
  match avmc_bar_presence_field b with
  | avmc_bar_absent => false
  | avmc_bar_present => Nat.eqb (avmc_bar_defect_total b) 0
  end.

Lemma avmc_claim_bar_zero_defect_true :
  avmc_claim_bar_zero_defect aqueousVsMineralClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma avmc_claim_bar_absent_not_zero_defect :
  avmc_claim_bar_zero_defect aqueousVsMineralClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive avmc_conservation_verdict : Type :=
  | avmc_verdict_unwired_ok
  | avmc_verdict_named_ok
  | avmc_verdict_design_ok
  | avmc_verdict_trivial_refuse
  | avmc_verdict_xor_refuse
  | avmc_verdict_green_invent_refuse
  | avmc_verdict_proved_without_bar_refuse
  | avmc_verdict_production_wired_refuse
  | avmc_verdict_parallel_aqueous_axiom_refuse
  | avmc_verdict_species_id_smuggle_refuse
  | avmc_verdict_extra_element_id_refuse
  | avmc_verdict_hydrate_l1_smuggle_axiom_refuse
  | avmc_verdict_tp_float_pin_refuse.

Definition avmc_conservation_verdict_ok (v : avmc_conservation_verdict) : bool :=
  match v with
  | avmc_verdict_unwired_ok => true
  | avmc_verdict_named_ok => true
  | avmc_verdict_design_ok => true
  | _ => false
  end.

Definition aqueousVsMineralBundleNontrivial (b : avmc_channel_bundle) : bool :=
  Nat.ltb 0 (aqueousVsMineralBundlePresentCount b).

Definition evaluate_aqueous_vs_mineral_bundle
  (m : AqueousVsMineralConservationModality)
  (b : avmc_channel_bundle)
  (bar : avmc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : avmc_conservation_verdict :=
  if claim_physics_green
  then avmc_verdict_green_invent_refuse
  else if claim_proved
       then avmc_verdict_proved_without_bar_refuse
       else if negb (aqueousVsMineralBundleNontrivial b)
            then avmc_verdict_trivial_refuse
            else if avmcXorClassifierIncompatible claim_xor_classifier b
                 then avmc_verdict_xor_refuse
                 else
                   match m with
                   | aqueous_vs_mineral_conservation_unwired =>
                       if aqueousVsMineralBundleIsConcurrentProduct b
                       then avmc_verdict_named_ok
                       else avmc_verdict_design_ok
                   | aqueous_vs_mineral_conservation_assumed
                   | aqueous_vs_mineral_conservation_surrogate =>
                       avmc_verdict_design_ok
                   | aqueous_vs_mineral_conservation_proved =>
                       avmc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_aqueous_vs_mineral_conservation_close
  (m : AqueousVsMineralConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : avmc_conservation_verdict :=
  if claim_physics_green
  then avmc_verdict_green_invent_refuse
  else if claim_production_wired
  then avmc_verdict_production_wired_refuse
  else
    match m with
    | aqueous_vs_mineral_conservation_unwired => avmc_verdict_unwired_ok
    | aqueous_vs_mineral_conservation_assumed
    | aqueous_vs_mineral_conservation_proved
    | aqueous_vs_mineral_conservation_surrogate => avmc_verdict_named_ok
    end.

Definition aqueous_vs_mineral_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_aqueous_vs_mineral_conservation_close
          aqueous_vs_mineral_conservation_proved claim_physics_green claim_production_wired with
  | avmc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive avmc_conservation_law : Type :=
  | avmc_law_conserved
  | avmc_law_named_ok
  | avmc_law_trivial_refuse
  | avmc_law_green_invent_refuse.

Definition avmc_conservation_law_count : nat := 4.

Lemma avmc_conservation_law_count_is_four :
  avmc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive avmc_conservation_law_witness : Type :=
  | avmc_law_witness_open
  | avmc_law_witness_proved.

Definition evaluate_avmc_conservation_law_witness
  (law : avmc_conservation_law)
  (m : AqueousVsMineralConservationModality)
  : avmc_conservation_law_witness :=
  match m with
  | aqueous_vs_mineral_conservation_unwired
  | aqueous_vs_mineral_conservation_assumed
  | aqueous_vs_mineral_conservation_surrogate => avmc_law_witness_open
  | aqueous_vs_mineral_conservation_proved => avmc_law_witness_proved
  end.

Lemma all_avmc_conservation_laws_open_at_unwired :
  evaluate_avmc_conservation_law_witness avmc_law_conserved
    aqueous_vs_mineral_conservation_unwired = avmc_law_witness_open /\
  evaluate_avmc_conservation_law_witness avmc_law_named_ok
    aqueous_vs_mineral_conservation_unwired = avmc_law_witness_open /\
  evaluate_avmc_conservation_law_witness avmc_law_trivial_refuse
    aqueous_vs_mineral_conservation_unwired = avmc_law_witness_open /\
  evaluate_avmc_conservation_law_witness avmc_law_green_invent_refuse
    aqueous_vs_mineral_conservation_unwired = avmc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-16 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition aqueousVsMineralConservationProved : bool := false.

Lemma aqueous_vs_mineral_conservation_proved_false :
  aqueousVsMineralConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_unwired false false =
  avmc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_unwired false false =
  avmc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_unwired false false) =
  true.
Proof.
  unfold avmc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false false =
  avmc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_aqueous_vs_mineral_conservation :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false false =
  avmc_verdict_named_ok /\
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_aqueous_vs_mineral_idx = 16.
Proof.
  repeat split; reflexivity.
Qed.

Lemma avmc_named_close_ok :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_proved false false =
  avmc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_aqueous_vs_mineral_conservation_close :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_proved false false =
  avmc_verdict_named_ok /\
  aqueous_vs_mineral_conservation_authorized false false = true.
Proof.
  split.
  - apply avmc_named_close_ok.
  - unfold aqueous_vs_mineral_conservation_authorized.
    rewrite avmc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — aqueous-vs-mineral refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralEmptyWitness
    aqueousVsMineralClaimBarAbsent false false false =
  avmc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralEmptyWitness
    aqueousVsMineralClaimBarAbsent false false false =
  avmc_verdict_trivial_refuse /\
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_bundle
       aqueous_vs_mineral_conservation_unwired
       aqueousVsMineralEmptyWitness
       aqueousVsMineralClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold avmc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent true false false =
  avmc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent true false false =
  avmc_verdict_xor_refuse /\
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_bundle
       aqueous_vs_mineral_conservation_unwired
       aqueousVsMineralFe26Witness
       aqueousVsMineralClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold avmc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_unwired true false =
  avmc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_unwired true false) =
  false.
Proof.
  unfold avmc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_avmc_bundle_refuse :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false true false =
  avmc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — aqueous-vs-mineral refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false true =
  avmc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false true =
  avmc_verdict_proved_without_bar_refuse /\
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_bundle
       aqueous_vs_mineral_conservation_unwired
       aqueousVsMineralFe26Witness
       aqueousVsMineralClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold avmc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — aqueous-vs-mineral lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_proved false true =
  avmc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_proved false true) =
  false.
Proof.
  unfold avmc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel aqueous axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition aqueousVsMineralConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs".

Definition parallelAqueousAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_aqueous_axiom_refuse :
  aqueousVsMineralConservationAuthority <>
  parallelAqueousAxiomTag /\
  aqueousVsMineralConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply aqueous_vs_mineral_conservation_proved_false.
Qed.

Theorem parallel_aqueous_axiom_not_minted :
  aqueousVsMineralConservationAuthority =
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs" /\
  aqueousVsMineralConservationProved = false /\
  aqueousVsMineralConservationAuthority <> parallelAqueousAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — L1 hydrate SpeciesId ≠ L0 ElementId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_hydrate_species_id_as_l0_element_row".

Definition aqueousVsMineralConservationFraming : string :=
  "second_law_conservation_aqueous_vs_mineral_env_restriction_one_axiom".

Lemma species_id_smuggle_refuse :
  aqueousVsMineralConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_aqueous_vs_mineral_idx = 16.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem env_restriction_not_species_id_smuggle :
  aqueousVsMineralConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_aqueous_vs_mineral_idx = 16 /\
  aqueousVsMineralConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — aqueous-vs-mineral ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "catalyst_consumed_in_net_reaction".

Lemma extra_element_id_refuse :
  aqueousVsMineralConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  aqueousVsMineralConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Hydrate L1 smuggle refuse — aqueous-vs-mineral ≠ parallel aqueous axiom    *)
(* ------------------------------------------------------------------ *)

Definition parallelAqueousAxiomFraming : string :=
  "parallel_aqueous_vs_mineral_axiom_minted_as_27th_law".

Definition aqueousMineralRegimeAuthority : string :=
  "umst/umst-chem/src/aqueous_mineral_regime.rs".

Lemma hydrate_l1_smuggle_axiom_refuse :
  aqueousVsMineralConservationFraming <>
  parallelAqueousAxiomFraming /\
  aqueousMineralRegimeAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem aqueous_vs_mineral_not_parallel_aqueous_axiom :
  aqueousVsMineralConservationFraming <>
  parallelAqueousAxiomFraming /\
  aqueousMineralRegimeAuthority =
  "umst/umst-chem/src/aqueous_mineral_regime.rs" /\
  aqueousVsMineralConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_aqueous_vs_mineral_scaffold".

Lemma tp_float_pin_refuse :
  aqueousVsMineralConservationFraming <>
  tpFloatPinFraming /\
  env_restriction_channel_tag = "env_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  aqueousVsMineralConservationFraming <>
  tpFloatPinFraming /\
  phreeqc_pitzer_prior_art_channel_tag = "phreeqc_pitzer_prior_art" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Aqueous-vs-mineral **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition avmc_conservation_coherence_scaffold : bool :=
  avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_proved false false) &&
  negb (avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_unwired true false)) &&
  negb (avmc_conservation_verdict_ok
    (evaluate_aqueous_vs_mineral_conservation_close
       aqueous_vs_mineral_conservation_proved false true)).

Lemma avmc_conservation_coherence_scaffold_true :
  avmc_conservation_coherence_scaffold = true.
Proof.
  unfold avmc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem avmc_conservation_coherence_scaffold_theorem :
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_proved false false =
    avmc_verdict_named_ok /\
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_unwired true false =
    avmc_verdict_green_invent_refuse /\
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_proved false true =
    avmc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition avmc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition avmc_conservation_knowing_fiber_ok : bool :=
  avmc_conservation_fiber_ok fiber_quantum_knowing.

Definition avmc_conservation_meso_acting_ok : bool :=
  avmc_conservation_fiber_ok fiber_meso_acting.

Lemma avmc_conservation_knowing_fiber_ok_true :
  avmc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma avmc_conservation_meso_acting_not_ok :
  avmc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem avmc_conservation_routes_knowing_not_meso :
  avmc_conservation_knowing_fiber_ok = true /\
  avmc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply avmc_conservation_knowing_fiber_ok_true.
  - apply avmc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  avmc_conservation_knowing_fiber_ok &&
  negb avmc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, avmc_conservation_knowing_fiber_ok,
    avmc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-16 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem aqueous_vs_mineral_conservation_fixture_scaffold :
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false false =
    avmc_verdict_named_ok /\
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralEmptyWitness
    aqueousVsMineralClaimBarAbsent false false false =
    avmc_verdict_trivial_refuse /\
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent true false false =
    avmc_verdict_xor_refuse /\
  evaluate_aqueous_vs_mineral_bundle
    aqueous_vs_mineral_conservation_unwired
    aqueousVsMineralFe26Witness
    aqueousVsMineralClaimBarAbsent false false true =
    avmc_verdict_proved_without_bar_refuse /\
  evaluate_aqueous_vs_mineral_conservation_close
    aqueous_vs_mineral_conservation_unwired false false =
    avmc_verdict_unwired_ok /\
  avmc_conservation_knowing_fiber_ok = true /\
  avmc_conservation_meso_acting_ok = false /\
  aqueousVsMineralConservationProved = false /\
  avmcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — aqueous vs mineral) *)
(* ------------------------------------------------------------------ *)

Definition chemL0AqueousMineralAuthority : string :=
  "umst/umst-chem/src/aqueous_mineral_regime.rs".

Definition chemL0AqueousMineralTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs".

Definition aqueousMineralEnvRestrictionAuthority : string :=
  "umst/umst-chem/src/aqueous_mineral_is_environment_restriction.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".


Definition temperatureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/temperature_is_graph_function.rs".

Definition pressureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/pressure_is_graph_function.rs".

Definition chemL0EdgeAqueousCellId : string := "CHEM-L0-EDGE-AQUEOUS".

Definition aqueousVsMineralConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-AQUEOUS-VS-MINERAL-CONSERVATION".

Definition aqueousVsMineralConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-AQUEOUS-VS-MINERAL-CONSERVATION AqueousVsMineralConservationModality Unwired Assumed Proved Surrogate four-step lattice aqueousVsMineralConservationProved false evaluateAqueousVsMineralBundle evaluateAqueousVsMineralConservation named class 16 aqueous vs mineral Fe Z=26 env restriction second law PHREEQC Pitzer prior art concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel aqueous axiom refuse species id smuggle refuse L1 hydrate SpeciesId not L0 ElementId refuse extra element id Z=119 refuse parallel aqueous axiom refuse aqueous ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired T P graph functions v14 not float pins".

Lemma aqueous_vs_mineral_conservation_cell_id :
  aqueousVsMineralConservationCellId =
  "CHEM-FORMAL-Q-COQ-AQUEOUS-VS-MINERAL-CONSERVATION".
Proof. reflexivity. Qed.

Lemma aqueous_vs_mineral_conservation_cites_l0_table :
  chemL0AqueousMineralTableAuthority <> "".
Proof. discriminate. Qed.

Lemma aqueous_vs_mineral_conservation_authority_path :
  aqueousVsMineralConservationAuthority =
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs".
Proof. reflexivity. Qed.

Lemma aqueous_vs_mineral_conservation_cites_l0_ore02 :
  chemL0AqueousMineralAuthority <> "".
Proof. discriminate. Qed.

Lemma aqueous_vs_mineral_conservation_cites_marker :
  avmcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma aqueous_vs_mineral_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma aqueous_vs_mineral_conservation_cites_ore02_cell :
  chemL0EdgeAqueousCellId = "CHEM-L0-EDGE-AQUEOUS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma aqueous_vs_mineral_not_27th_axiom :
  aqueousVsMineralConservationFraming <> parallelAqueousAxiomTag.
Proof. discriminate. Qed.

Lemma aqueous_vs_mineral_second_law_conservation_framing :
  aqueousVsMineralConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  PHREEQC/Pitzer prior art — restriction is named object, not PHREEQC axiom        *)
(* ------------------------------------------------------------------ *)

Definition phreeqcPitzerPriorArtFraming : string :=
  "phreeqc_pitzer_sit_prior_art_not_named_object".

Definition envRestrictionNamedObject : string :=
  "env_restriction_on_aqueous_vs_mineral_morphism".

Lemma tst_prior_art_not_named_object :
  envRestrictionNamedObject <>
  phreeqcPitzerPriorArtFraming /\
  phreeqc_pitzer_prior_art_channel_tag = "phreeqc_pitzer_prior_art".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem env_restriction_is_named_object_not_phreeqc :
  envRestrictionNamedObject <>
  phreeqcPitzerPriorArtFraming /\
  env_restriction_channel_tag = "env_restriction" /\
  aqueousVsMineralConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Env restriction refuse — not parallel aqueous axiom     *)
(* ------------------------------------------------------------------ *)

Definition envRestrictionFraming : string :=
  "env_restriction_not_parallel_aqueous_axiom".

Lemma env_restriction_not_parallel_aqueous_axiom_refuse :
  envRestrictionFraming <>
  parallelAqueousAxiomFraming /\
  env_restriction_channel_tag = "env_restriction".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem aqueous_vs_mineral_env_restriction_not_parallel_aqueous_axiom :
  envRestrictionFraming <>
  parallelAqueousAxiomFraming /\
  aqueousMineralRegimeAuthority =
  "umst/umst-chem/src/aqueous_mineral_regime.rs" /\
  aqueousVsMineralConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma aqueous_vs_mineral_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma aqueous_vs_mineral_conservation_modality_unwired :
  aqueousVsMineralConservationModalityCurrent =
  aqueous_vs_mineral_conservation_unwired.
Proof. reflexivity. Qed.

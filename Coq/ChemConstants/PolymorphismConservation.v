(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PolymorphismConservation.v                            *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 18 **polymorphism** **conservation**.     *)
(*  Polymorphism is same stoichiometry, distinct lattice geometries    *)
(*  (α/β/γ) — **not** allotrope-specific (class 10) and not a new     *)
(*  ElementId. Concurrent Π_c PatternBundle factor — **product** not   *)
(*  XOR. T/P are graph functions (v14) — not bare float pins.          *)
(*  polymorphismConservationProved false. Modality Unwired.            *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/polymorphism_geometry.rs (read-only cite). *)
(*  INT: umst/umst-chem/src/l0_tables/polymorphism.rs (read-only cite).*)
(*  INT: umst/umst-chem/src/temperature_is_graph_function.rs (cite).   *)
(*  INT: umst/umst-chem/src/pressure_is_graph_function.rs (cite).      *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-18 **polymorphism** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PolymorphismConservationModality : Type :=
  | polymorphism_conservation_unwired
  | polymorphism_conservation_assumed
  | polymorphism_conservation_proved
  | polymorphism_conservation_surrogate.

Definition polymorphismConservationModalityCurrent :
  PolymorphismConservationModality :=
  polymorphism_conservation_unwired.

Definition polymorphism_lattice_cardinality : nat := 4.

Lemma polymorphism_lattice_cardinality_is_four :
  polymorphism_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma polymorphism_lattice_not_118_squared :
  negb (Nat.eqb polymorphism_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold polymorphism_lattice_cardinality.
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

(* North-star §2 class 18 — polymorphism concurrent Π_c factor. *)
Definition pattern_class_polymorphism_idx : nat := 18.

Lemma pattern_class_polymorphism_idx_is_18 :
  pattern_class_polymorphism_idx = 18.
Proof. reflexivity. Qed.

Lemma polymorphism_class_index_valid :
  pattern_class_index_valid pattern_class_polymorphism_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_polymorphism_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierPolymorphismRowId : string := "X18".

Lemma cross_classifier_polymorphism_row_named :
  crossClassifierPolymorphismRowId = "X18".
Proof. reflexivity. Qed.

Definition pattern_class_polymorphism_tag : string :=
  "polymorphism".

Definition north_star_class_18_polymorphism_tag : string :=
  "class 18 polymorphism".

Lemma pattern_class_polymorphism_tag_nonempty :
  pattern_class_polymorphism_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_18_polymorphism_tag_nonempty :
  north_star_class_18_polymorphism_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Si Z=14 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition silicon_atomic_number_z : nat := 14.

Lemma silicon_atomic_number_z_is_14 :
  silicon_atomic_number_z = 14.
Proof. reflexivity. Qed.

Definition silicon_z_valid : bool :=
  Nat.ltb 0 silicon_atomic_number_z &&
  Nat.leb silicon_atomic_number_z iupac_table_cardinality.

Lemma silicon_z_valid_true : silicon_z_valid = true.
Proof.
  unfold silicon_z_valid, silicon_atomic_number_z, iupac_table_cardinality.
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

Definition polymorphism_factor_tag : string :=
  "polymorphism".

Definition stoichiometry_invariant_channel_tag : string := "stoichiometry_invariant".

Definition lattice_geometry_variant_channel_tag : string := "lattice_geometry_variant".

Lemma polymorphism_factor_tag_nonempty :
  polymorphism_factor_tag <> "".
Proof. discriminate. Qed.

Lemma stoichiometry_invariant_channel_tag_nonempty :
  stoichiometry_invariant_channel_tag <> "".
Proof. discriminate. Qed.

Lemma lattice_geometry_variant_channel_tag_nonempty :
  lattice_geometry_variant_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Polymorphism product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive pcv_channel_slot : Type :=
  | pcv_slot_unwired
  | pcv_slot_absent
  | pcv_slot_present.

Definition pcv_channel_slot_beq (s1 s2 : pcv_channel_slot) : bool :=
  match s1, s2 with
  | pcv_slot_unwired, pcv_slot_unwired => true
  | pcv_slot_absent, pcv_slot_absent => true
  | pcv_slot_present, pcv_slot_present => true
  | _, _ => false
  end.

Definition pcv_channel_slot_is_present (s : pcv_channel_slot) : bool :=
  match s with
  | pcv_slot_present => true
  | _ => false
  end.

Definition polymorphismProductChannelCount : nat := 3.

Lemma polymorphism_product_channel_count_is_three :
  polymorphismProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = stoichiometry invariant, 1 = lattice geometry variant, 2 = class 18 polymorphism. *)
Definition pcv_channel_stoichiometry_invariant : nat := 0.
Definition pcv_channel_lattice_geometry_variant : nat := 1.
Definition pcv_channel_class18_polymorphism : nat := 2.

Lemma pcv_channel_stoichiometry_invariant_idx_is_0 :
  pcv_channel_stoichiometry_invariant = 0.
Proof. reflexivity. Qed.

Lemma pcv_channel_lattice_geometry_variant_idx_is_1 :
  pcv_channel_lattice_geometry_variant = 1.
Proof. reflexivity. Qed.

Lemma pcv_channel_class18_polymorphism_idx_is_2 :
  pcv_channel_class18_polymorphism = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Polymorphism concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition pcv_channel_bundle : Type := nat -> pcv_channel_slot.

Definition polymorphismBundleAllUnwired : pcv_channel_bundle :=
  fun _ => pcv_slot_unwired.

Definition polymorphismBundleAt (b : pcv_channel_bundle) (idx : nat)
  (slot : pcv_channel_slot) : pcv_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition polymorphismBundleWithPresent
  (b : pcv_channel_bundle) (idx : nat) : pcv_channel_bundle :=
  polymorphismBundleAt b idx pcv_slot_present.

Fixpoint count_pcv_present_up_to (b : pcv_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if pcv_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_pcv_present_up_to b i + add
  end.

Definition polymorphismBundlePresentCount (b : pcv_channel_bundle) : nat :=
  count_pcv_present_up_to b polymorphismProductChannelCount.

Definition polymorphismBundleHolds (b : pcv_channel_bundle) (idx : nat) : bool :=
  pcv_channel_slot_is_present (b idx).

Definition polymorphismBundleIsConcurrentProduct (b : pcv_channel_bundle) : bool :=
  Nat.leb 2 (polymorphismBundlePresentCount b).

(* Si Z=14 stoichiometry invariant + lattice geometry variant + class 18 polymorphism concurrent witness. *)
Definition polymorphismSi14Witness : pcv_channel_bundle :=
  polymorphismBundleWithPresent
    (polymorphismBundleWithPresent
      (polymorphismBundleWithPresent polymorphismBundleAllUnwired
        pcv_channel_stoichiometry_invariant)
      pcv_channel_lattice_geometry_variant)
    pcv_channel_class18_polymorphism.

Definition polymorphismEmptyWitness : pcv_channel_bundle :=
  polymorphismBundleAllUnwired.

Definition polymorphismSinglePresent : pcv_channel_bundle :=
  polymorphismBundleWithPresent polymorphismBundleAllUnwired
    pcv_channel_stoichiometry_invariant.

Lemma stoichiometry_invariant_channel_present :
  polymorphismBundleHolds polymorphismSi14Witness
    pcv_channel_stoichiometry_invariant = true.
Proof. reflexivity. Qed.

Lemma lattice_geometry_variant_channel_present :
  polymorphismBundleHolds polymorphismSi14Witness
    pcv_channel_lattice_geometry_variant = true.
Proof. reflexivity. Qed.

Lemma class18_polymorphism_channel_present :
  polymorphismBundleHolds polymorphismSi14Witness
    pcv_channel_class18_polymorphism = true.
Proof. reflexivity. Qed.

Lemma si14_witness_present_count_is_three :
  polymorphismBundlePresentCount polymorphismSi14Witness = 3.
Proof. reflexivity. Qed.

Lemma si14_witness_is_concurrent_product :
  polymorphismBundleIsConcurrentProduct polymorphismSi14Witness = true.
Proof.
  unfold polymorphismBundleIsConcurrentProduct.
  rewrite si14_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  polymorphismBundlePresentCount polymorphismEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  polymorphismBundleIsConcurrentProduct polymorphismEmptyWitness = false.
Proof.
  unfold polymorphismBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  polymorphismBundlePresentCount polymorphismSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  polymorphismBundleIsConcurrentProduct polymorphismSinglePresent = false.
Proof.
  unfold polymorphismBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive pcv_xor_posture : Type :=
  | pcv_xor_exclusive
  | pcv_xor_concurrent_product.

Definition prcXorClassifierMarker : string := "chem_l0_polymorphism_xor_classifier_v1".
Definition prcConcurrentProductMarker : string := "chem_int_polymorphism_product_v1".

Lemma pcv_xor_marker_ne_concurrent_product_marker :
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition prcXorClassifierIncompatible (claim_xor : bool)
  (b : pcv_channel_bundle) : bool :=
  claim_xor && polymorphismBundleIsConcurrentProduct b.

Lemma pcv_xor_refuse_on_si14_witness :
  prcXorClassifierIncompatible true polymorphismSi14Witness = true.
Proof.
  unfold prcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma pcv_xor_ok_on_concurrent_product_claim :
  prcXorClassifierIncompatible false polymorphismSi14Witness = false.
Proof. reflexivity. Qed.

Definition prcProductNotXor : bool :=
  polymorphismBundleIsConcurrentProduct polymorphismSi14Witness &&
  prcXorClassifierIncompatible true polymorphismSi14Witness.

Lemma pcv_product_not_xor_true : prcProductNotXor = true.
Proof.
  unfold prcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  prcProductNotXor = true /\
  Nat.leb 2 (polymorphismBundlePresentCount
    polymorphismSi14Witness) = true /\
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof.
  split.
  - apply pcv_product_not_xor_true.
  - split.
    + rewrite si14_witness_present_count_is_three.
      reflexivity.
    + apply pcv_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Polymorphism **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive pcv_bar_presence : Type :=
  | pcv_bar_absent
  | pcv_bar_present.

Record pcv_claim_bar : Type := {
  pcv_bar_presence_field : pcv_bar_presence;
  pcv_bar_defect_total : nat
}.

Definition polymorphismClaimBarAbsent : pcv_claim_bar :=
  {| pcv_bar_presence_field := pcv_bar_absent;
     pcv_bar_defect_total := 0 |}.

Definition polymorphismClaimBarZeroDefect : pcv_claim_bar :=
  {| pcv_bar_presence_field := pcv_bar_present;
     pcv_bar_defect_total := 0 |}.

Definition pcv_claim_bar_zero_defect (b : pcv_claim_bar) : bool :=
  match pcv_bar_presence_field b with
  | pcv_bar_absent => false
  | pcv_bar_present => Nat.eqb (pcv_bar_defect_total b) 0
  end.

Lemma pcv_claim_bar_zero_defect_true :
  pcv_claim_bar_zero_defect polymorphismClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma pcv_claim_bar_absent_not_zero_defect :
  pcv_claim_bar_zero_defect polymorphismClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Polymorphism **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive pcv_conservation_verdict : Type :=
  | pcv_verdict_unwired_ok
  | pcv_verdict_named_ok
  | pcv_verdict_design_ok
  | pcv_verdict_trivial_refuse
  | pcv_verdict_xor_refuse
  | pcv_verdict_green_invent_refuse
  | pcv_verdict_proved_without_bar_refuse
  | pcv_verdict_production_wired_refuse
  | pcv_verdict_parallel_polymorphism_axiom_refuse
  | pcv_verdict_allotrope_specific_smuggle_refuse
  | pcv_verdict_extra_element_id_refuse
  | pcv_verdict_allotrope_specific_force_refuse
  | pcv_verdict_tp_float_pin_refuse.

Definition pcv_conservation_verdict_ok (v : pcv_conservation_verdict) : bool :=
  match v with
  | pcv_verdict_unwired_ok => true
  | pcv_verdict_named_ok => true
  | pcv_verdict_design_ok => true
  | _ => false
  end.

Definition polymorphismBundleNontrivial (b : pcv_channel_bundle) : bool :=
  Nat.ltb 0 (polymorphismBundlePresentCount b).

Definition evaluate_polymorphism_bundle
  (m : PolymorphismConservationModality)
  (b : pcv_channel_bundle)
  (bar : pcv_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : pcv_conservation_verdict :=
  if claim_physics_green
  then pcv_verdict_green_invent_refuse
  else if claim_proved
       then pcv_verdict_proved_without_bar_refuse
       else if negb (polymorphismBundleNontrivial b)
            then pcv_verdict_trivial_refuse
            else if prcXorClassifierIncompatible claim_xor_classifier b
                 then pcv_verdict_xor_refuse
                 else
                   match m with
                   | polymorphism_conservation_unwired =>
                       if polymorphismBundleIsConcurrentProduct b
                       then pcv_verdict_named_ok
                       else pcv_verdict_design_ok
                   | polymorphism_conservation_assumed
                   | polymorphism_conservation_surrogate =>
                       pcv_verdict_design_ok
                   | polymorphism_conservation_proved =>
                       pcv_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_polymorphism_conservation_close
  (m : PolymorphismConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : pcv_conservation_verdict :=
  if claim_physics_green
  then pcv_verdict_green_invent_refuse
  else if claim_production_wired
  then pcv_verdict_production_wired_refuse
  else
    match m with
    | polymorphism_conservation_unwired => pcv_verdict_unwired_ok
    | polymorphism_conservation_assumed
    | polymorphism_conservation_proved
    | polymorphism_conservation_surrogate => pcv_verdict_named_ok
    end.

Definition polymorphism_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_polymorphism_conservation_close
          polymorphism_conservation_proved claim_physics_green claim_production_wired with
  | pcv_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Polymorphism **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive pcv_conservation_law : Type :=
  | pcv_law_conserved
  | pcv_law_named_ok
  | pcv_law_trivial_refuse
  | pcv_law_green_invent_refuse.

Definition pcv_conservation_law_count : nat := 4.

Lemma pcv_conservation_law_count_is_four :
  pcv_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive pcv_conservation_law_witness : Type :=
  | pcv_law_witness_open
  | pcv_law_witness_proved.

Definition evaluate_pcv_conservation_law_witness
  (law : pcv_conservation_law)
  (m : PolymorphismConservationModality)
  : pcv_conservation_law_witness :=
  match m with
  | polymorphism_conservation_unwired
  | polymorphism_conservation_assumed
  | polymorphism_conservation_surrogate => pcv_law_witness_open
  | polymorphism_conservation_proved => pcv_law_witness_proved
  end.

Lemma all_pcv_conservation_laws_open_at_unwired :
  evaluate_pcv_conservation_law_witness pcv_law_conserved
    polymorphism_conservation_unwired = pcv_law_witness_open /\
  evaluate_pcv_conservation_law_witness pcv_law_named_ok
    polymorphism_conservation_unwired = pcv_law_witness_open /\
  evaluate_pcv_conservation_law_witness pcv_law_trivial_refuse
    polymorphism_conservation_unwired = pcv_law_witness_open /\
  evaluate_pcv_conservation_law_witness pcv_law_green_invent_refuse
    polymorphism_conservation_unwired = pcv_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-18 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition polymorphismConservationProved : bool := false.

Lemma polymorphism_conservation_proved_false :
  polymorphismConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_unwired false false =
  pcv_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_unwired false false =
  pcv_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_unwired false false) =
  true.
Proof.
  unfold pcv_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Si Z=14 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma si14_witness_named_ok :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false false =
  pcv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_si14_polymorphism_conservation :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false false =
  pcv_verdict_named_ok /\
  polymorphismBundleIsConcurrentProduct polymorphismSi14Witness = true /\
  silicon_atomic_number_z = 14 /\
  pattern_class_polymorphism_idx = 18.
Proof.
  repeat split; reflexivity.
Qed.

Lemma pcv_named_close_ok :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_proved false false =
  pcv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_polymorphism_conservation_close :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_proved false false =
  pcv_verdict_named_ok /\
  polymorphism_conservation_authorized false false = true.
Proof.
  split.
  - apply pcv_named_close_ok.
  - unfold polymorphism_conservation_authorized.
    rewrite pcv_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — polymorphism refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismEmptyWitness
    polymorphismClaimBarAbsent false false false =
  pcv_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismEmptyWitness
    polymorphismClaimBarAbsent false false false =
  pcv_verdict_trivial_refuse /\
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_bundle
       polymorphism_conservation_unwired
       polymorphismEmptyWitness
       polymorphismClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold pcv_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent true false false =
  pcv_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent true false false =
  pcv_verdict_xor_refuse /\
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_bundle
       polymorphism_conservation_unwired
       polymorphismSi14Witness
       polymorphismClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold pcv_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_unwired true false =
  pcv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_unwired true false) =
  false.
Proof.
  unfold pcv_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_pcv_bundle_refuse :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false true false =
  pcv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — polymorphism refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false true =
  pcv_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false true =
  pcv_verdict_proved_without_bar_refuse /\
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_bundle
       polymorphism_conservation_unwired
       polymorphismSi14Witness
       polymorphismClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold pcv_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — polymorphism lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_proved false true =
  pcv_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_proved false true) =
  false.
Proof.
  unfold pcv_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel polymorphism axiom refuse — morphism not parallel polymorphism axiom      *)
(* ------------------------------------------------------------------ *)

Definition polymorphismConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/polymorphism.rs".

Definition parallelPolymorphismAxiomTag : string := "parallel_polymorphism_axiom".

Lemma parallel_polymorphism_axiom_refuse :
  polymorphismConservationAuthority <>
  parallelPolymorphismAxiomTag /\
  polymorphismConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply polymorphism_conservation_proved_false.
Qed.

Theorem parallel_polymorphism_axiom_not_minted :
  polymorphismConservationAuthority =
  "umst/umst-chem/src/l0_tables/polymorphism.rs" /\
  polymorphismConservationProved = false /\
  polymorphismConservationAuthority <> parallelPolymorphismAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Allotrope-specific smuggle refuse — polymorphism ≠ class 10 allotrope          *)
(* ------------------------------------------------------------------ *)

Definition allotropeSpecificSmuggleFraming : string :=
  "lattice_geometry_variant_not_named_object".

Definition polymorphismConservationFraming : string :=
  "second_law_conservation_polymorphism_stoichiometry_invariant_one_axiom".

Lemma allotrope_specific_smuggle_refuse :
  polymorphismConservationFraming <>
  allotropeSpecificSmuggleFraming /\
  silicon_atomic_number_z = 14 /\
  pattern_class_polymorphism_idx = 18.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem stoichiometry_invariant_not_allotrope_specific_smuggle :
  polymorphismConservationFraming <>
  allotropeSpecificSmuggleFraming /\
  silicon_atomic_number_z = 14 /\
  pattern_class_polymorphism_idx = 18 /\
  polymorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — polymorphism ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "new_element_id_on_polymorphism_morphism".

Lemma extra_element_id_refuse :
  polymorphismConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  polymorphismConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  silicon_atomic_number_z = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — polymorphism ≠ extra polymorphism force axiom    *)
(* ------------------------------------------------------------------ *)

Definition allotropeSpecificForceFraming : string :=
  "allotrope_specific_force_axiom_minted_as_parallel_polymorphism_law".

Definition polymorphismGeometryAuthority : string :=
  "umst/umst-chem/src/polymorphism_geometry.rs".

Lemma allotrope_specific_force_refuse :
  polymorphismConservationFraming <>
  allotropeSpecificForceFraming /\
  polymorphismGeometryAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem polymorphism_not_allotrope_specific_force :
  polymorphismConservationFraming <>
  allotropeSpecificForceFraming /\
  polymorphismGeometryAuthority =
  "umst/umst-chem/src/polymorphism_geometry.rs" /\
  polymorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_polymorphism_scaffold".

Lemma tp_float_pin_refuse :
  polymorphismConservationFraming <>
  tpFloatPinFraming /\
  stoichiometry_invariant_channel_tag = "stoichiometry_invariant".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  polymorphismConservationFraming <>
  tpFloatPinFraming /\
  lattice_geometry_variant_channel_tag = "lattice_geometry_variant" /\
  silicon_atomic_number_z = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Polymorphism **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition pcv_conservation_coherence_scaffold : bool :=
  pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_proved false false) &&
  negb (pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_unwired true false)) &&
  negb (pcv_conservation_verdict_ok
    (evaluate_polymorphism_conservation_close
       polymorphism_conservation_proved false true)).

Lemma pcv_conservation_coherence_scaffold_true :
  pcv_conservation_coherence_scaffold = true.
Proof.
  unfold pcv_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem pcv_conservation_coherence_scaffold_theorem :
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_proved false false =
    pcv_verdict_named_ok /\
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_unwired true false =
    pcv_verdict_green_invent_refuse /\
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_proved false true =
    pcv_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition pcv_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition pcv_conservation_knowing_fiber_ok : bool :=
  pcv_conservation_fiber_ok fiber_quantum_knowing.

Definition pcv_conservation_meso_acting_ok : bool :=
  pcv_conservation_fiber_ok fiber_meso_acting.

Lemma pcv_conservation_knowing_fiber_ok_true :
  pcv_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma pcv_conservation_meso_acting_not_ok :
  pcv_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem pcv_conservation_routes_knowing_not_meso :
  pcv_conservation_knowing_fiber_ok = true /\
  pcv_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply pcv_conservation_knowing_fiber_ok_true.
  - apply pcv_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  pcv_conservation_knowing_fiber_ok &&
  negb pcv_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, pcv_conservation_knowing_fiber_ok,
    pcv_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-18 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem polymorphism_conservation_fixture_scaffold :
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false false =
    pcv_verdict_named_ok /\
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismEmptyWitness
    polymorphismClaimBarAbsent false false false =
    pcv_verdict_trivial_refuse /\
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent true false false =
    pcv_verdict_xor_refuse /\
  evaluate_polymorphism_bundle
    polymorphism_conservation_unwired
    polymorphismSi14Witness
    polymorphismClaimBarAbsent false false true =
    pcv_verdict_proved_without_bar_refuse /\
  evaluate_polymorphism_conservation_close
    polymorphism_conservation_unwired false false =
    pcv_verdict_unwired_ok /\
  pcv_conservation_knowing_fiber_ok = true /\
  pcv_conservation_meso_acting_ok = false /\
  polymorphismConservationProved = false /\
  prcProductNotXor = true /\
  silicon_atomic_number_z = 14.
Proof.
  repeat split; reflexivity.
Qed.


Definition temperatureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/temperature_is_graph_function.rs".

Definition pressureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/pressure_is_graph_function.rs".

Definition chemIntTemperatureIsGraphFunctionCellId : string :=
  "CHEM-INT-TEMPERATURE-IS-GRAPH-FUNCTION".

Definition chemIntPressureIsGraphFunctionCellId : string :=
  "CHEM-INT-PRESSURE-IS-GRAPH-FUNCTION".

Lemma temperature_graph_function_authority_named :
  temperatureGraphFunctionAuthority <> "".
Proof. discriminate. Qed.

Lemma pressure_graph_function_authority_named :
  pressureGraphFunctionAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — polymorphism) *)
(* ------------------------------------------------------------------ *)

Definition chemL0PolymorphismTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/polymorphism.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgePolymorphismCellId : string := "CHEM-L0-EDGE-POLY".

Definition polymorphismConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-POLYMORPHISM-CONSERVATION".

Definition polymorphismConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-POLYMORPHISM-CONSERVATION PolymorphismConservationModality Unwired Assumed Proved Surrogate four-step lattice polymorphismConservationProved false evaluatePolymorphismBundle evaluatePolymorphismConservation named class 18 polymorphism Si Z=14 stoichiometry invariant lattice geometry alpha beta gamma second law concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel polymorphism axiom refuse allotrope specific class 10 refuse extra element id Z=119 refuse allotrope specific force refuse polymorphism ne AllotropeSpecific Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired T P graph functions v14 not float pins".

Lemma polymorphism_conservation_cell_id :
  polymorphismConservationCellId =
  "CHEM-FORMAL-Q-COQ-POLYMORPHISM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma polymorphism_conservation_cites_l0_table :
  chemL0PolymorphismTableAuthority <> "".
Proof. discriminate. Qed.

Lemma polymorphism_conservation_authority_path :
  polymorphismConservationAuthority =
  "umst/umst-chem/src/l0_tables/polymorphism.rs".
Proof. reflexivity. Qed.

Lemma polymorphism_conservation_cites_l0_ore02 :
  chemL0PolymorphismTableAuthority <> "".
Proof. discriminate. Qed.

Lemma polymorphism_conservation_cites_marker :
  prcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma polymorphism_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma polymorphism_conservation_cites_ore02_cell :
  chemL0EdgePolymorphismCellId = "CHEM-L0-EDGE-POLY".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not parallel polymorphism axiom    *)
(* ------------------------------------------------------------------ *)

Lemma polymorphism_not_parallel_axiom :
  polymorphismConservationFraming <> parallelPolymorphismAxiomTag.
Proof. discriminate. Qed.

Lemma polymorphism_second_law_conservation_framing :
  polymorphismConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Allotrope-specific refuse — polymorphism ≠ class 10 allotrope       *)
(* ------------------------------------------------------------------ *)

Definition allotropeClass10Framing : string :=
  "allotrope_class_10_element_geometry_not_polymorphism".

Definition allotropeClass10Index : nat := 10.

Lemma allotrope_class10_index_is_10 :
  allotropeClass10Index = 10.
Proof. reflexivity. Qed.

Lemma polymorphism_not_allotrope_class10 :
  pattern_class_polymorphism_idx <> allotropeClass10Index /\
  pattern_class_polymorphism_idx = 18.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem polymorphism_same_stoichiometry_not_allotrope_specific :
  allotropeClass10Framing <>
  polymorphismConservationFraming /\
  pattern_class_polymorphism_idx = 18 /\
  allotropeClass10Index = 10 /\
  polymorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Definition polymorphismNamedObject : string :=
  "stoichiometry_invariant_on_polymorphism_morphism".

Lemma lattice_geometry_variant_not_named_object :
  polymorphismNamedObject <>
  allotropeClass10Framing /\
  lattice_geometry_variant_channel_tag = "lattice_geometry_variant".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem stoichiometry_invariant_is_named_object_not_allotrope :
  polymorphismNamedObject <>
  allotropeClass10Framing /\
  stoichiometry_invariant_channel_tag = "stoichiometry_invariant" /\
  polymorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Stoichiometry invariant refuse — not allotrope-specific force       *)
(* ------------------------------------------------------------------ *)

Definition stoichiometryInvariantFraming : string :=
  "stoichiometry_invariant_not_extra_force".

Lemma stoichiometry_invariant_not_extra_force_refuse :
  stoichiometryInvariantFraming <>
  allotropeSpecificForceFraming /\
  stoichiometry_invariant_channel_tag = "stoichiometry_invariant".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem polymorphism_stoichiometry_invariant_not_extra_force :
  stoichiometryInvariantFraming <>
  allotropeSpecificForceFraming /\
  polymorphismGeometryAuthority =
  "umst/umst-chem/src/polymorphism_geometry.rs" /\
  polymorphismConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma polymorphism_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma polymorphism_conservation_modality_unwired :
  polymorphismConservationModalityCurrent =
  polymorphism_conservation_unwired.
Proof. reflexivity. Qed.

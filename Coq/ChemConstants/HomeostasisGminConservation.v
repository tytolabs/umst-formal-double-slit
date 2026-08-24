(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: HomeostasisGminConservation.v                          *)
(*                                                                      *)
(*  Knowing-fiber Coq: constitutive homeostasis_gmin conservation.        *)
(*  Homeostasis is **G-min** on the same second-law + conservation      *)
(*  object (not a biology axiom / negative-feedback smuggle).           *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Constitutive chart named; G-min common-tangent is prior presentation. *)
(*  homeostasisGminConservationProved false. Modality Unwired.         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs (cite). *)
(*  INT: umst/umst-chem/src/l0_tables/assemblage_stability_why.rs (cite).*)
(*  INT: umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs.  *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-7 **homeostasis_gmin** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive HomeostasisGminConservationModality : Type :=
  | homeostasis_gmin_conservation_unwired
  | homeostasis_gmin_conservation_assumed
  | homeostasis_gmin_conservation_proved
  | homeostasis_gmin_conservation_surrogate.

Definition homeostasisGminConservationModalityCurrent :
  HomeostasisGminConservationModality :=
  homeostasis_gmin_conservation_unwired.

Definition homeostasis_gmin_lattice_cardinality : nat := 4.

Lemma homeostasis_gmin_lattice_cardinality_is_four :
  homeostasis_gmin_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma homeostasis_gmin_lattice_not_118_squared :
  negb (Nat.eqb homeostasis_gmin_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold homeostasis_gmin_lattice_cardinality.
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

(* North-star §2 class 7 — homeostasis_gmin G-min anchor concurrent Π_c factor. *)
Definition pattern_class_homeostasis_gmin_anchor_idx : nat := 7.

Lemma pattern_class_homeostasis_gmin_anchor_idx_is_7 :
  pattern_class_homeostasis_gmin_anchor_idx = 7.
Proof. reflexivity. Qed.

Lemma homeostasis_gmin_class_index_valid :
  pattern_class_index_valid pattern_class_homeostasis_gmin_anchor_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_homeostasis_gmin_anchor_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierHomeostasisGminRowId : string := "X07".

Lemma cross_classifier_homeostasis_gmin_row_named :
  crossClassifierHomeostasisGminRowId = "X07".
Proof. reflexivity. Qed.

Definition pattern_class_homeostasis_gmin_tag : string :=
  "homeostasis_gmin".

Definition north_star_class_7_g_min_anchor_tag : string :=
  "class 7 G-min anchor".

Lemma pattern_class_homeostasis_gmin_tag_nonempty :
  pattern_class_homeostasis_gmin_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_7_g_min_anchor_tag_nonempty :
  north_star_class_7_g_min_anchor_tag <> "".
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

Definition homeostasis_gmin_factor_tag : string :=
  "homeostasis_gmin".

Definition g_min_common_tangent_channel_tag : string := "g_min_common_tangent".

Definition constitutive_chart_not_biology_channel_tag : string := "constitutive_chart_not_biology".

Lemma homeostasis_gmin_factor_tag_nonempty :
  homeostasis_gmin_factor_tag <> "".
Proof. discriminate. Qed.

Lemma g_min_common_tangent_channel_tag_nonempty :
  g_min_common_tangent_channel_tag <> "".
Proof. discriminate. Qed.

Lemma constitutive_chart_not_biology_channel_tag_nonempty :
  constitutive_chart_not_biology_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive hgcv_channel_slot : Type :=
  | hgcv_slot_unwired
  | hgcv_slot_absent
  | hgcv_slot_present.

Definition hgcv_channel_slot_beq (s1 s2 : hgcv_channel_slot) : bool :=
  match s1, s2 with
  | hgcv_slot_unwired, hgcv_slot_unwired => true
  | hgcv_slot_absent, hgcv_slot_absent => true
  | hgcv_slot_present, hgcv_slot_present => true
  | _, _ => false
  end.

Definition hgcv_channel_slot_is_present (s : hgcv_channel_slot) : bool :=
  match s with
  | hgcv_slot_present => true
  | _ => false
  end.

Definition homeostasisGminProductChannelCount : nat := 3.

Lemma homeostasis_gmin_product_channel_count_is_three :
  homeostasisGminProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = G-min common tangent, 1 = constitutive chart not biology, 2 = homeostasis_gmin chart. *)
Definition hgcv_channel_g_min_common_tangent : nat := 0.
Definition hgcv_channel_constitutive_chart_not_biology : nat := 1.
Definition hgcv_channel_homeostasis_gmin_chart : nat := 2.

Lemma hgcv_channel_g_min_common_tangent_idx_is_0 :
  hgcv_channel_g_min_common_tangent = 0.
Proof. reflexivity. Qed.

Lemma hgcv_channel_constitutive_chart_not_biology_idx_is_1 :
  hgcv_channel_constitutive_chart_not_biology = 1.
Proof. reflexivity. Qed.

Lemma hgcv_channel_homeostasis_gmin_chart_idx_is_2 :
  hgcv_channel_homeostasis_gmin_chart = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition ccv_channel_bundle : Type := nat -> hgcv_channel_slot.

Definition homeostasisGminBundleAllUnwired : ccv_channel_bundle :=
  fun _ => hgcv_slot_unwired.

Definition homeostasisGminBundleAt (b : ccv_channel_bundle) (idx : nat)
  (slot : hgcv_channel_slot) : ccv_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition homeostasisGminBundleWithPresent
  (b : ccv_channel_bundle) (idx : nat) : ccv_channel_bundle :=
  homeostasisGminBundleAt b idx hgcv_slot_present.

Fixpoint count_hgcv_present_up_to (b : ccv_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if hgcv_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_hgcv_present_up_to b i + add
  end.

Definition homeostasisGminBundlePresentCount (b : ccv_channel_bundle) : nat :=
  count_hgcv_present_up_to b homeostasisGminProductChannelCount.

Definition homeostasisGminBundleHolds (b : ccv_channel_bundle) (idx : nat) : bool :=
  hgcv_channel_slot_is_present (b idx).

Definition homeostasisGminBundleIsConcurrentProduct (b : ccv_channel_bundle) : bool :=
  Nat.leb 2 (homeostasisGminBundlePresentCount b).

(* Pt Z=78 G-min common tangent + constitutive chart + homeostasis_gmin concurrent witness. *)
Definition homeostasisGminPt78Witness : ccv_channel_bundle :=
  homeostasisGminBundleWithPresent
    (homeostasisGminBundleWithPresent
      (homeostasisGminBundleWithPresent homeostasisGminBundleAllUnwired
        hgcv_channel_g_min_common_tangent)
      hgcv_channel_constitutive_chart_not_biology)
    hgcv_channel_homeostasis_gmin_chart.

Definition homeostasisGminEmptyWitness : ccv_channel_bundle :=
  homeostasisGminBundleAllUnwired.

Definition homeostasisGminSinglePresent : ccv_channel_bundle :=
  homeostasisGminBundleWithPresent homeostasisGminBundleAllUnwired
    hgcv_channel_g_min_common_tangent.

Lemma g_min_common_tangent_channel_present :
  homeostasisGminBundleHolds homeostasisGminPt78Witness
    hgcv_channel_g_min_common_tangent = true.
Proof. reflexivity. Qed.

Lemma constitutive_chart_not_biology_channel_present :
  homeostasisGminBundleHolds homeostasisGminPt78Witness
    hgcv_channel_constitutive_chart_not_biology = true.
Proof. reflexivity. Qed.

Lemma homeostasis_gmin_chart_channel_present :
  homeostasisGminBundleHolds homeostasisGminPt78Witness
    hgcv_channel_homeostasis_gmin_chart = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  homeostasisGminBundlePresentCount homeostasisGminPt78Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  homeostasisGminBundleIsConcurrentProduct homeostasisGminPt78Witness = true.
Proof.
  unfold homeostasisGminBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  homeostasisGminBundlePresentCount homeostasisGminEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  homeostasisGminBundleIsConcurrentProduct homeostasisGminEmptyWitness = false.
Proof.
  unfold homeostasisGminBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  homeostasisGminBundlePresentCount homeostasisGminSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  homeostasisGminBundleIsConcurrentProduct homeostasisGminSinglePresent = false.
Proof.
  unfold homeostasisGminBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive hgcv_xor_posture : Type :=
  | hgcv_xor_exclusive
  | hgcv_xor_concurrent_product.

Definition hgcvXorClassifierMarker : string := "chem_l0_homeostasis_gmin_xor_classifier_v1".
Definition hgcvConcurrentProductMarker : string := "chem_int_homeostasis_gmin_product_v1".

Lemma hgcv_xor_marker_ne_concurrent_product_marker :
  hgcvXorClassifierMarker <> hgcvConcurrentProductMarker.
Proof. discriminate. Qed.

Definition hgcvXorClassifierIncompatible (claim_xor : bool)
  (b : ccv_channel_bundle) : bool :=
  claim_xor && homeostasisGminBundleIsConcurrentProduct b.

Lemma hgcv_xor_refuse_on_pt78_witness :
  hgcvXorClassifierIncompatible true homeostasisGminPt78Witness = true.
Proof.
  unfold hgcvXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma hgcv_xor_ok_on_concurrent_product_claim :
  hgcvXorClassifierIncompatible false homeostasisGminPt78Witness = false.
Proof. reflexivity. Qed.

Definition hgcvProductNotXor : bool :=
  homeostasisGminBundleIsConcurrentProduct homeostasisGminPt78Witness &&
  hgcvXorClassifierIncompatible true homeostasisGminPt78Witness.

Lemma hgcv_product_not_xor_true : hgcvProductNotXor = true.
Proof.
  unfold hgcvProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  hgcvProductNotXor = true /\
  Nat.leb 2 (homeostasisGminBundlePresentCount
    homeostasisGminPt78Witness) = true /\
  hgcvXorClassifierMarker <> hgcvConcurrentProductMarker.
Proof.
  split.
  - apply hgcv_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply hgcv_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive hgcv_bar_presence : Type :=
  | hgcv_bar_absent
  | hgcv_bar_present.

Record hgcv_claim_bar : Type := {
  hgcv_bar_presence_field : hgcv_bar_presence;
  hgcv_bar_defect_total : nat
}.

Definition homeostasisGminClaimBarAbsent : hgcv_claim_bar :=
  {| hgcv_bar_presence_field := hgcv_bar_absent;
     hgcv_bar_defect_total := 0 |}.

Definition homeostasisGminClaimBarZeroDefect : hgcv_claim_bar :=
  {| hgcv_bar_presence_field := hgcv_bar_present;
     hgcv_bar_defect_total := 0 |}.

Definition hgcv_claim_bar_zero_defect (b : hgcv_claim_bar) : bool :=
  match hgcv_bar_presence_field b with
  | hgcv_bar_absent => false
  | hgcv_bar_present => Nat.eqb (hgcv_bar_defect_total b) 0
  end.

Lemma hgcv_claim_bar_zero_defect_true :
  hgcv_claim_bar_zero_defect homeostasisGminClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma hgcv_claim_bar_absent_not_zero_defect :
  hgcv_claim_bar_zero_defect homeostasisGminClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive hgcv_conservation_verdict : Type :=
  | hgcv_verdict_unwired_ok
  | hgcv_verdict_named_ok
  | hgcv_verdict_design_ok
  | hgcv_verdict_trivial_refuse
  | hgcv_verdict_xor_refuse
  | hgcv_verdict_green_invent_refuse
  | hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse
  | hgcv_verdict_homeostasis_gmin_production_wired_refuse
  | hgcv_verdict_parallel_biology_axiom_refuse
  | hgcv_verdict_species_id_smuggle_refuse
  | hgcv_verdict_extra_element_id_refuse
  | hgcv_verdict_extra_biology_axiom_refuse
  | hgcv_verdict_tp_float_pin_refuse.

Definition hgcv_conservation_verdict_ok (v : hgcv_conservation_verdict) : bool :=
  match v with
  | hgcv_verdict_unwired_ok => true
  | hgcv_verdict_named_ok => true
  | hgcv_verdict_design_ok => true
  | _ => false
  end.

Definition homeostasisGminBundleNontrivial (b : ccv_channel_bundle) : bool :=
  Nat.ltb 0 (homeostasisGminBundlePresentCount b).

Definition evaluate_homeostasis_gmin_bundle
  (m : HomeostasisGminConservationModality)
  (b : ccv_channel_bundle)
  (bar : hgcv_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : hgcv_conservation_verdict :=
  if claim_physics_green
  then hgcv_verdict_green_invent_refuse
  else if claim_proved
       then hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse
       else if negb (homeostasisGminBundleNontrivial b)
            then hgcv_verdict_trivial_refuse
            else if hgcvXorClassifierIncompatible claim_xor_classifier b
                 then hgcv_verdict_xor_refuse
                 else
                   match m with
                   | homeostasis_gmin_conservation_unwired =>
                       if homeostasisGminBundleIsConcurrentProduct b
                       then hgcv_verdict_named_ok
                       else hgcv_verdict_design_ok
                   | homeostasis_gmin_conservation_assumed
                   | homeostasis_gmin_conservation_surrogate =>
                       hgcv_verdict_design_ok
                   | homeostasis_gmin_conservation_proved =>
                       hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse
                   end.

Definition evaluate_homeostasis_gmin_conservation_close
  (m : HomeostasisGminConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : hgcv_conservation_verdict :=
  if claim_physics_green
  then hgcv_verdict_green_invent_refuse
  else if claim_production_wired
  then hgcv_verdict_homeostasis_gmin_production_wired_refuse
  else
    match m with
    | homeostasis_gmin_conservation_unwired => hgcv_verdict_unwired_ok
    | homeostasis_gmin_conservation_assumed
    | homeostasis_gmin_conservation_proved
    | homeostasis_gmin_conservation_surrogate => hgcv_verdict_named_ok
    end.

Definition homeostasis_gmin_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_homeostasis_gmin_conservation_close
          homeostasis_gmin_conservation_proved claim_physics_green claim_production_wired with
  | hgcv_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive hgcv_conservation_law : Type :=
  | hgcv_law_conserved
  | hgcv_law_named_ok
  | hgcv_law_trivial_refuse
  | hgcv_law_green_invent_refuse.

Definition hgcv_conservation_law_count : nat := 4.

Lemma hgcv_conservation_law_count_is_four :
  hgcv_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive hgcv_conservation_law_witness : Type :=
  | hgcv_law_witness_open
  | hgcv_law_witness_proved.

Definition evaluate_hgcv_conservation_law_witness
  (law : hgcv_conservation_law)
  (m : HomeostasisGminConservationModality)
  : hgcv_conservation_law_witness :=
  match m with
  | homeostasis_gmin_conservation_unwired
  | homeostasis_gmin_conservation_assumed
  | homeostasis_gmin_conservation_surrogate => hgcv_law_witness_open
  | homeostasis_gmin_conservation_proved => hgcv_law_witness_proved
  end.

Lemma all_hgcv_conservation_laws_open_at_unwired :
  evaluate_hgcv_conservation_law_witness hgcv_law_conserved
    homeostasis_gmin_conservation_unwired = hgcv_law_witness_open /\
  evaluate_hgcv_conservation_law_witness hgcv_law_named_ok
    homeostasis_gmin_conservation_unwired = hgcv_law_witness_open /\
  evaluate_hgcv_conservation_law_witness hgcv_law_trivial_refuse
    homeostasis_gmin_conservation_unwired = hgcv_law_witness_open /\
  evaluate_hgcv_conservation_law_witness hgcv_law_green_invent_refuse
    homeostasis_gmin_conservation_unwired = hgcv_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-7 G-min anchor pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition homeostasisGminConservationProved : bool := false.

Lemma homeostasis_gmin_conservation_proved_false :
  homeostasisGminConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_unwired_close_without_production_wiring :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_unwired false false =
  hgcv_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_unwired_modality_always_ok_without_production_wiring :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_unwired false false =
  hgcv_verdict_unwired_ok.
Proof. apply homeostasis_gmin_unwired_close_without_production_wiring. Qed.

Lemma homeostasis_gmin_unwired_verdict_ok_without_production_wiring :
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_unwired false false) =
  true.
Proof.
  unfold hgcv_conservation_verdict_ok.
  rewrite homeostasis_gmin_unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_pt78_witness_named_ok :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false false =
  hgcv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_homeostasis_gmin_conservation :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false false =
  hgcv_verdict_named_ok /\
  homeostasisGminBundleIsConcurrentProduct homeostasisGminPt78Witness = true /\
  platinum_atomic_number_z = 78 /\
  pattern_class_homeostasis_gmin_anchor_idx = 7.
Proof.
  repeat split; reflexivity.
Qed.

Lemma hgcv_named_close_ok :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_proved false false =
  hgcv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_homeostasis_gmin_conservation_close :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_proved false false =
  hgcv_verdict_named_ok /\
  homeostasis_gmin_conservation_authorized false false = true.
Proof.
  split.
  - apply hgcv_named_close_ok.
  - unfold homeostasis_gmin_conservation_authorized.
    rewrite hgcv_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — homeostasis_gmin refuse *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_trivial_bundle_refused :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminEmptyWitness
    homeostasisGminClaimBarAbsent false false false =
  hgcv_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_trivial_empty_bundle_fail_closed :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminEmptyWitness
    homeostasisGminClaimBarAbsent false false false =
  hgcv_verdict_trivial_refuse /\
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_bundle
       homeostasis_gmin_conservation_unwired
       homeostasisGminEmptyWitness
       homeostasisGminClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply homeostasis_gmin_trivial_bundle_refused.
  - unfold hgcv_conservation_verdict_ok.
    rewrite homeostasis_gmin_trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_xor_classifier_refused :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent true false false =
  hgcv_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_xor_mutually_exclusive_classifier_fail_closed :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent true false false =
  hgcv_verdict_xor_refuse /\
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_bundle
       homeostasis_gmin_conservation_unwired
       homeostasisGminPt78Witness
       homeostasisGminClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply homeostasis_gmin_xor_classifier_refused.
  - unfold hgcv_conservation_verdict_ok.
    rewrite homeostasis_gmin_xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_green_invent_refuse_unwired :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_unwired true false =
  hgcv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_green_invent_always_refuse :
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_unwired true false) =
  false.
Proof.
  unfold hgcv_conservation_verdict_ok.
  rewrite homeostasis_gmin_green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma homeostasis_gmin_green_invent_bundle_refuse :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false true false =
  hgcv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — homeostasis_gmin refuse   *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_proved_without_bar_refuse :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false true =
  hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_proved_without_bar_fail_closed :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false true =
  hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse /\
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_bundle
       homeostasis_gmin_conservation_unwired
       homeostasisGminPt78Witness
       homeostasisGminClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply homeostasis_gmin_proved_without_bar_refuse.
  - unfold hgcv_conservation_verdict_ok.
    rewrite homeostasis_gmin_proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — homeostasis_gmin lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_production_wired_refuse :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_proved false true =
  hgcv_verdict_homeostasis_gmin_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem homeostasis_gmin_production_wired_claim_refused :
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_proved false true) =
  false.
Proof.
  unfold hgcv_conservation_verdict_ok.
  rewrite homeostasis_gmin_production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel biology axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition homeostasisGminConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".

Definition parallelBiologyAxiomTag : string := "biology_homeostasis_axiom".

Lemma parallel_biology_axiom_refuse :
  homeostasisGminConservationAuthority <>
  parallelBiologyAxiomTag /\
  homeostasisGminConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply homeostasis_gmin_conservation_proved_false.
Qed.

Theorem parallel_biology_axiom_not_minted :
  homeostasisGminConservationAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs" /\
  homeostasisGminConservationProved = false /\
  homeostasisGminConservationAuthority <> parallelBiologyAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — G-min ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "biology_axiom_not_named_object".

Definition homeostasisGminConservationFraming : string :=
  "second_law_conservation_homeostasis_gmin_g_min_one_axiom".

Lemma species_id_smuggle_refuse :
  homeostasisGminConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_homeostasis_gmin_anchor_idx = 7.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem g_min_not_species_id_smuggle :
  homeostasisGminConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_homeostasis_gmin_anchor_idx = 7 /\
  homeostasisGminConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — homeostasis_gmin ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "biology_sensor_actuator_smuggle".

Lemma extra_element_id_refuse :
  homeostasisGminConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  homeostasisGminConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Biology axiom refuse — homeostasis_gmin ≠ biology axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraBiologyAxiomFraming : string :=
  "biology_homeostasis_axiom_minted_as_26th_law".

Definition gibbsConvexHullAuthority : string :=
  "umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs".

Lemma extra_biology_axiom_refuse :
  homeostasisGminConservationFraming <>
  extraBiologyAxiomFraming /\
  gibbsConvexHullAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem homeostasis_gmin_not_extra_biology_axiom :
  homeostasisGminConservationFraming <>
  extraBiologyAxiomFraming /\
  gibbsConvexHullAuthority =
  "umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs" /\
  homeostasisGminConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_homeostasis_gmin_scaffold".

Lemma tp_float_pin_refuse :
  homeostasisGminConservationFraming <>
  tpFloatPinFraming /\
  g_min_common_tangent_channel_tag = "g_min_common_tangent".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  homeostasisGminConservationFraming <>
  tpFloatPinFraming /\
  constitutive_chart_not_biology_channel_tag = "constitutive_chart_not_biology" /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  HomeostasisGmin **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition hgcv_conservation_coherence_scaffold : bool :=
  hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_proved false false) &&
  negb (hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_unwired true false)) &&
  negb (hgcv_conservation_verdict_ok
    (evaluate_homeostasis_gmin_conservation_close
       homeostasis_gmin_conservation_proved false true)).

Lemma hgcv_conservation_coherence_scaffold_true :
  hgcv_conservation_coherence_scaffold = true.
Proof.
  unfold hgcv_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem hgcv_conservation_coherence_scaffold_theorem :
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_proved false false =
    hgcv_verdict_named_ok /\
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_unwired true false =
    hgcv_verdict_green_invent_refuse /\
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_proved false true =
    hgcv_verdict_homeostasis_gmin_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition hgcv_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition hgcv_conservation_knowing_fiber_ok : bool :=
  hgcv_conservation_fiber_ok fiber_quantum_knowing.

Definition hgcv_conservation_meso_acting_ok : bool :=
  hgcv_conservation_fiber_ok fiber_meso_acting.

Lemma hgcv_conservation_knowing_fiber_ok_true :
  hgcv_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma hgcv_conservation_meso_acting_not_ok :
  hgcv_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem hgcv_conservation_routes_knowing_not_meso :
  hgcv_conservation_knowing_fiber_ok = true /\
  hgcv_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply hgcv_conservation_knowing_fiber_ok_true.
  - apply hgcv_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  hgcv_conservation_knowing_fiber_ok &&
  negb hgcv_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, hgcv_conservation_knowing_fiber_ok,
    hgcv_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named homeostasis_gmin + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem homeostasis_gmin_conservation_fixture_scaffold :
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false false =
    hgcv_verdict_named_ok /\
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminEmptyWitness
    homeostasisGminClaimBarAbsent false false false =
    hgcv_verdict_trivial_refuse /\
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent true false false =
    hgcv_verdict_xor_refuse /\
  evaluate_homeostasis_gmin_bundle
    homeostasis_gmin_conservation_unwired
    homeostasisGminPt78Witness
    homeostasisGminClaimBarAbsent false false true =
    hgcv_verdict_homeostasis_gmin_proved_without_bar_refuse /\
  evaluate_homeostasis_gmin_conservation_close
    homeostasis_gmin_conservation_unwired false false =
    hgcv_verdict_unwired_ok /\
  hgcv_conservation_knowing_fiber_ok = true /\
  hgcv_conservation_meso_acting_ok = false /\
  homeostasisGminConservationProved = false /\
  hgcvProductNotXor = true /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — homeostasis_gmin) *)
(* ------------------------------------------------------------------ *)

Definition chemPhysicsChartIsomorphismAuthority : string :=
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs".

Definition assemblageStabilityWhyTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemMathGibbsConvexHullCellId : string := "CHEM-MATH-GIBBS-CONVEX-HULL".

Definition homeostasisGminConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-HOMEOSTASIS-GMIN-CONSERVATION".

Definition homeostasisGminConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-HOMEOSTASIS-GMIN-CONSERVATION HomeostasisGminConservationModality Unwired Assumed Proved Surrogate four-step lattice homeostasisGminConservationProved false evaluateHomeostasisGminBundle evaluateHomeostasisGminConservation named homeostasis_gmin G-min common tangent Pt Z=78 constitutive chart second law concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel biology axiom refuse species id smuggle refuse extra element id Z=119 refuse extra biology axiom refuse homeostasis_gmin ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma homeostasis_gmin_conservation_cell_id :
  homeostasisGminConservationCellId =
  "CHEM-FORMAL-Q-COQ-HOMEOSTASIS-GMIN-CONSERVATION".
Proof. reflexivity. Qed.

Lemma homeostasis_gmin_conservation_cites_assemblage_table :
  assemblageStabilityWhyTableAuthority <> "".
Proof. discriminate. Qed.

Lemma homeostasis_gmin_conservation_authority_path :
  homeostasisGminConservationAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".
Proof. reflexivity. Qed.

Lemma homeostasis_gmin_conservation_cites_chem_physics_chart :
  chemPhysicsChartIsomorphismAuthority <> "".
Proof. discriminate. Qed.

Lemma homeostasis_gmin_conservation_cites_marker :
  hgcvConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma homeostasis_gmin_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma homeostasis_gmin_conservation_cites_gibbs_hull_cell :
  chemMathGibbsConvexHullCellId = "CHEM-MATH-GIBBS-CONVEX-HULL".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma homeostasis_gmin_not_26th_axiom :
  homeostasisGminConservationFraming <> parallelBiologyAxiomTag.
Proof. discriminate. Qed.

Lemma homeostasis_gmin_second_law_conservation_framing :
  homeostasisGminConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Biology axiom refuse — G-min is named object, not biology axiom        *)
(* ------------------------------------------------------------------ *)

Definition biologyAxiomFraming : string :=
  "biology_negative_feedback_homeostasis_not_named_object".

Definition gMinCommonTangentNamedObject : string :=
  "g_min_common_tangent_on_homeostasis_gmin_chart".

Lemma biology_axiom_not_named_object :
  gMinCommonTangentNamedObject <>
  biologyAxiomFraming /\
  constitutive_chart_not_biology_channel_tag = "constitutive_chart_not_biology".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem g_min_is_named_object_not_biology :
  gMinCommonTangentNamedObject <>
  biologyAxiomFraming /\
  g_min_common_tangent_channel_tag = "g_min_common_tangent" /\
  homeostasisGminConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  G-min presentation refuse — not biology axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition gMinPresentationFraming : string :=
  "g_min_presentation_not_biology_axiom".

Lemma g_min_not_extra_biology_refuse :
  gMinPresentationFraming <>
  extraBiologyAxiomFraming /\
  g_min_common_tangent_channel_tag = "g_min_common_tangent".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem homeostasis_gmin_g_min_not_extra_biology :
  gMinPresentationFraming <>
  extraBiologyAxiomFraming /\
  gibbsConvexHullAuthority =
  "umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs" /\
  homeostasisGminConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma homeostasis_gmin_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma homeostasis_gmin_conservation_modality_unwired :
  homeostasisGminConservationModalityCurrent =
  homeostasis_gmin_conservation_unwired.
Proof. reflexivity. Qed.

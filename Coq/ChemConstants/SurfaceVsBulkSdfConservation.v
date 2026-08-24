(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: SurfaceVsBulkSdfConservation.v                        *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 15 **surface_vs_bulk_sdf** **conservation**. *)
(*  Surface versus bulk is a geometry slice on the same object (not a    *)
(*  26th axiom). Catalysis lives here as Interact restriction. Concurrent *)
(*  Π_c PatternBundle factor — **product** not XOR.                       *)
(*  surfaceVsBulkSdfConservationProved false. Modality Unwired.           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/pattern_taxonomy.rs (read-only cite).       *)
(*  INT: umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs       *)
(*  (read-only cite). PatternProductConservation.v sibling.             *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-15 **surface_vs_bulk_sdf** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive SurfaceVsBulkSdfConservationModality : Type :=
  | surface_vs_bulk_sdf_conservation_unwired
  | surface_vs_bulk_sdf_conservation_assumed
  | surface_vs_bulk_sdf_conservation_proved
  | surface_vs_bulk_sdf_conservation_surrogate.

Definition surfaceVsBulkSdfConservationModalityCurrent :
  SurfaceVsBulkSdfConservationModality :=
  surface_vs_bulk_sdf_conservation_unwired.

Definition surface_vs_bulk_sdf_lattice_cardinality : nat := 4.

Lemma surface_vs_bulk_sdf_lattice_cardinality_is_four :
  surface_vs_bulk_sdf_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma surface_vs_bulk_sdf_lattice_not_118_squared :
  negb (Nat.eqb surface_vs_bulk_sdf_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold surface_vs_bulk_sdf_lattice_cardinality.
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

(* North-star §2 class 15 — surface_vs_bulk_sdf concurrent Π_c factor. *)
Definition pattern_class_surface_vs_bulk_sdf_idx : nat := 9.

Lemma pattern_class_surface_vs_bulk_sdf_idx_is_9 :
  pattern_class_surface_vs_bulk_sdf_idx = 9.
Proof. reflexivity. Qed.

Lemma surface_vs_bulk_sdf_class_index_valid :
  pattern_class_index_valid pattern_class_surface_vs_bulk_sdf_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_surface_vs_bulk_sdf_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierSurfaceVsBulkSdfRowId : string := "X15".

Lemma cross_classifier_surface_vs_bulk_sdf_row_named :
  crossClassifierSurfaceVsBulkSdfRowId = "X15".
Proof. reflexivity. Qed.

Definition pattern_class_surface_vs_bulk_sdf_tag : string :=
  "surface_vs_bulk_sdf".

Definition north_star_class_15_surface_vs_bulk_sdf_tag : string :=
  "class 15 surface vs bulk sdf".

Lemma pattern_class_surface_vs_bulk_sdf_tag_nonempty :
  pattern_class_surface_vs_bulk_sdf_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_15_surface_vs_bulk_sdf_tag_nonempty :
  north_star_class_15_surface_vs_bulk_sdf_tag <> "".
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

Definition surface_vs_bulk_sdf_factor_tag : string :=
  "surface_vs_bulk_sdf".

Definition geometry_slice_same_object_tag : string := "geometry_slice_same_object".

Definition catalysis_interact_restriction_tag : string := "catalysis_interact_restriction".

Lemma surface_vs_bulk_sdf_factor_tag_nonempty :
  surface_vs_bulk_sdf_factor_tag <> "".
Proof. discriminate. Qed.

Lemma geometry_slice_same_object_tag_nonempty :
  geometry_slice_same_object_tag <> "".
Proof. discriminate. Qed.

Lemma catalysis_interact_restriction_tag_nonempty :
  catalysis_interact_restriction_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive svbs_channel_slot : Type :=
  | svbs_slot_unwired
  | svbs_slot_absent
  | svbs_slot_present.

Definition svbs_channel_slot_beq (s1 s2 : svbs_channel_slot) : bool :=
  match s1, s2 with
  | svbs_slot_unwired, svbs_slot_unwired => true
  | svbs_slot_absent, svbs_slot_absent => true
  | svbs_slot_present, svbs_slot_present => true
  | _, _ => false
  end.

Definition svbs_channel_slot_is_present (s : svbs_channel_slot) : bool :=
  match s with
  | svbs_slot_present => true
  | _ => false
  end.

Definition surfaceVsBulkSdfProductChannelCount : nat := 3.

Lemma surface_vs_bulk_sdf_product_channel_count_is_three :
  surfaceVsBulkSdfProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = geometry slice, 1 = G-min second law, 2 = class 15. *)
Definition svbs_channel_geometry_slice : nat := 0.
Definition svbs_channel_catalysis_interact_restriction : nat := 1.
Definition svbs_channel_class15_surface_vs_bulk_sdf : nat := 2.

Lemma svbs_channel_geometry_slice_idx_is_0 :
  svbs_channel_geometry_slice = 0.
Proof. reflexivity. Qed.

Lemma svbs_channel_catalysis_interact_restriction_idx_is_1 :
  svbs_channel_catalysis_interact_restriction = 1.
Proof. reflexivity. Qed.

Lemma svbs_channel_class15_surface_vs_bulk_sdf_idx_is_2 :
  svbs_channel_class15_surface_vs_bulk_sdf = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition svbs_channel_bundle : Type := nat -> svbs_channel_slot.

Definition surfaceVsBulkSdfBundleAllUnwired : svbs_channel_bundle :=
  fun _ => svbs_slot_unwired.

Definition surfaceVsBulkSdfBundleAt (b : svbs_channel_bundle) (idx : nat)
  (slot : svbs_channel_slot) : svbs_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition surfaceVsBulkSdfBundleWithPresent
  (b : svbs_channel_bundle) (idx : nat) : svbs_channel_bundle :=
  surfaceVsBulkSdfBundleAt b idx svbs_slot_present.

Fixpoint count_svbs_present_up_to (b : svbs_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if svbs_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_svbs_present_up_to b i + add
  end.

Definition surfaceVsBulkSdfBundlePresentCount (b : svbs_channel_bundle) : nat :=
  count_svbs_present_up_to b surfaceVsBulkSdfProductChannelCount.

Definition surfaceVsBulkSdfBundleHolds (b : svbs_channel_bundle) (idx : nat) : bool :=
  svbs_channel_slot_is_present (b idx).

Definition surfaceVsBulkSdfBundleIsConcurrentProduct (b : svbs_channel_bundle) : bool :=
  Nat.leb 2 (surfaceVsBulkSdfBundlePresentCount b).

(* Pt Z=78 geometry slice + G-min + class-15 surface vs bulk sdf concurrent witness. *)
Definition surfaceVsBulkSdfPt78Witness : svbs_channel_bundle :=
  surfaceVsBulkSdfBundleWithPresent
    (surfaceVsBulkSdfBundleWithPresent
      (surfaceVsBulkSdfBundleWithPresent surfaceVsBulkSdfBundleAllUnwired
        svbs_channel_geometry_slice)
      svbs_channel_catalysis_interact_restriction)
    svbs_channel_class15_surface_vs_bulk_sdf.

Definition surfaceVsBulkSdfEmptyWitness : svbs_channel_bundle :=
  surfaceVsBulkSdfBundleAllUnwired.

Definition surfaceVsBulkSdfSinglePresent : svbs_channel_bundle :=
  surfaceVsBulkSdfBundleWithPresent surfaceVsBulkSdfBundleAllUnwired
    svbs_channel_geometry_slice.

Lemma geometry_slice_channel_present :
  surfaceVsBulkSdfBundleHolds surfaceVsBulkSdfPt78Witness
    svbs_channel_geometry_slice = true.
Proof. reflexivity. Qed.

Lemma catalysis_interact_restriction_channel_present :
  surfaceVsBulkSdfBundleHolds surfaceVsBulkSdfPt78Witness
    svbs_channel_catalysis_interact_restriction = true.
Proof. reflexivity. Qed.

Lemma class15_surface_vs_bulk_sdf_channel_present :
  surfaceVsBulkSdfBundleHolds surfaceVsBulkSdfPt78Witness
    svbs_channel_class15_surface_vs_bulk_sdf = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  surfaceVsBulkSdfBundlePresentCount surfaceVsBulkSdfPt78Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfPt78Witness = true.
Proof.
  unfold surfaceVsBulkSdfBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  surfaceVsBulkSdfBundlePresentCount surfaceVsBulkSdfEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfEmptyWitness = false.
Proof.
  unfold surfaceVsBulkSdfBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  surfaceVsBulkSdfBundlePresentCount surfaceVsBulkSdfSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfSinglePresent = false.
Proof.
  unfold surfaceVsBulkSdfBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive svbs_xor_posture : Type :=
  | svbs_xor_exclusive
  | svbs_xor_concurrent_product.

Definition svbsXorClassifierMarker : string := "chem_l0_surface_vs_bulk_sdf_xor_classifier_v1".
Definition svbsConcurrentProductMarker : string := "chem_int_surface_vs_bulk_sdf_product_v1".

Lemma svbs_xor_marker_ne_concurrent_product_marker :
  svbsXorClassifierMarker <> svbsConcurrentProductMarker.
Proof. discriminate. Qed.

Definition svbsXorClassifierIncompatible (claim_xor : bool)
  (b : svbs_channel_bundle) : bool :=
  claim_xor && surfaceVsBulkSdfBundleIsConcurrentProduct b.

Lemma svbs_xor_refuse_on_pt78_witness :
  svbsXorClassifierIncompatible true surfaceVsBulkSdfPt78Witness = true.
Proof.
  unfold svbsXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma svbs_xor_ok_on_concurrent_product_claim :
  svbsXorClassifierIncompatible false surfaceVsBulkSdfPt78Witness = false.
Proof. reflexivity. Qed.

Definition svbsProductNotXor : bool :=
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfPt78Witness &&
  svbsXorClassifierIncompatible true surfaceVsBulkSdfPt78Witness.

Lemma svbs_product_not_xor_true : svbsProductNotXor = true.
Proof.
  unfold svbsProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  svbsProductNotXor = true /\
  Nat.leb 2 (surfaceVsBulkSdfBundlePresentCount
    surfaceVsBulkSdfPt78Witness) = true /\
  svbsXorClassifierMarker <> svbsConcurrentProductMarker.
Proof.
  split.
  - apply svbs_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply svbs_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive svbs_bar_presence : Type :=
  | svbs_bar_absent
  | svbs_bar_present.

Record svbs_claim_bar : Type := {
  svbs_bar_presence_field : svbs_bar_presence;
  svbs_bar_defect_total : nat
}.

Definition surfaceVsBulkSdfClaimBarAbsent : svbs_claim_bar :=
  {| svbs_bar_presence_field := svbs_bar_absent;
     svbs_bar_defect_total := 0 |}.

Definition surfaceVsBulkSdfClaimBarZeroDefect : svbs_claim_bar :=
  {| svbs_bar_presence_field := svbs_bar_present;
     svbs_bar_defect_total := 0 |}.

Definition svbs_claim_bar_zero_defect (b : svbs_claim_bar) : bool :=
  match svbs_bar_presence_field b with
  | svbs_bar_absent => false
  | svbs_bar_present => Nat.eqb (svbs_bar_defect_total b) 0
  end.

Lemma svbs_claim_bar_zero_defect_true :
  svbs_claim_bar_zero_defect surfaceVsBulkSdfClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma svbs_claim_bar_absent_not_zero_defect :
  svbs_claim_bar_zero_defect surfaceVsBulkSdfClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive svbs_conservation_verdict : Type :=
  | svbs_verdict_unwired_ok
  | svbs_verdict_named_ok
  | svbs_verdict_design_ok
  | svbs_verdict_trivial_refuse
  | svbs_verdict_xor_refuse
  | svbs_verdict_green_invent_refuse
  | svbs_verdict_proved_without_bar_refuse
  | svbs_verdict_production_wired_refuse
  | svbs_verdict_parallel_surface_vs_bulk_sdf_axiom_refuse
  | svbs_verdict_species_id_smuggle_refuse
  | svbs_verdict_extra_element_id_refuse
  | svbs_verdict_free_purification_refuse
  | svbs_verdict_tp_float_pin_refuse.

Definition svbs_conservation_verdict_ok (v : svbs_conservation_verdict) : bool :=
  match v with
  | svbs_verdict_unwired_ok => true
  | svbs_verdict_named_ok => true
  | svbs_verdict_design_ok => true
  | _ => false
  end.

Definition surfaceVsBulkSdfBundleNontrivial (b : svbs_channel_bundle) : bool :=
  Nat.ltb 0 (surfaceVsBulkSdfBundlePresentCount b).

Definition evaluate_surface_vs_bulk_sdf_bundle
  (m : SurfaceVsBulkSdfConservationModality)
  (b : svbs_channel_bundle)
  (bar : svbs_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : svbs_conservation_verdict :=
  if claim_physics_green
  then svbs_verdict_green_invent_refuse
  else if claim_proved
       then svbs_verdict_proved_without_bar_refuse
       else if negb (surfaceVsBulkSdfBundleNontrivial b)
            then svbs_verdict_trivial_refuse
            else if svbsXorClassifierIncompatible claim_xor_classifier b
                 then svbs_verdict_xor_refuse
                 else
                   match m with
                   | surface_vs_bulk_sdf_conservation_unwired =>
                       if surfaceVsBulkSdfBundleIsConcurrentProduct b
                       then svbs_verdict_named_ok
                       else svbs_verdict_design_ok
                   | surface_vs_bulk_sdf_conservation_assumed
                   | surface_vs_bulk_sdf_conservation_surrogate =>
                       svbs_verdict_design_ok
                   | surface_vs_bulk_sdf_conservation_proved =>
                       svbs_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_surface_vs_bulk_sdf_conservation_close
  (m : SurfaceVsBulkSdfConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : svbs_conservation_verdict :=
  if claim_physics_green
  then svbs_verdict_green_invent_refuse
  else if claim_production_wired
  then svbs_verdict_production_wired_refuse
  else
    match m with
    | surface_vs_bulk_sdf_conservation_unwired => svbs_verdict_unwired_ok
    | surface_vs_bulk_sdf_conservation_assumed
    | surface_vs_bulk_sdf_conservation_proved
    | surface_vs_bulk_sdf_conservation_surrogate => svbs_verdict_named_ok
    end.

Definition surface_vs_bulk_sdf_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_surface_vs_bulk_sdf_conservation_close
          surface_vs_bulk_sdf_conservation_proved claim_physics_green claim_production_wired with
  | svbs_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive svbs_conservation_law : Type :=
  | svbs_law_conserved
  | svbs_law_named_ok
  | svbs_law_trivial_refuse
  | svbs_law_green_invent_refuse.

Definition svbs_conservation_law_count : nat := 4.

Lemma svbs_conservation_law_count_is_four :
  svbs_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive svbs_conservation_law_witness : Type :=
  | svbs_law_witness_open
  | svbs_law_witness_proved.

Definition evaluate_svbs_conservation_law_witness
  (law : svbs_conservation_law)
  (m : SurfaceVsBulkSdfConservationModality)
  : svbs_conservation_law_witness :=
  match m with
  | surface_vs_bulk_sdf_conservation_unwired
  | surface_vs_bulk_sdf_conservation_assumed
  | surface_vs_bulk_sdf_conservation_surrogate => svbs_law_witness_open
  | surface_vs_bulk_sdf_conservation_proved => svbs_law_witness_proved
  end.

Lemma all_svbs_conservation_laws_open_at_unwired :
  evaluate_svbs_conservation_law_witness svbs_law_conserved
    surface_vs_bulk_sdf_conservation_unwired = svbs_law_witness_open /\
  evaluate_svbs_conservation_law_witness svbs_law_named_ok
    surface_vs_bulk_sdf_conservation_unwired = svbs_law_witness_open /\
  evaluate_svbs_conservation_law_witness svbs_law_trivial_refuse
    surface_vs_bulk_sdf_conservation_unwired = svbs_law_witness_open /\
  evaluate_svbs_conservation_law_witness svbs_law_green_invent_refuse
    surface_vs_bulk_sdf_conservation_unwired = svbs_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-15 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition surfaceVsBulkSdfConservationProved : bool := false.

Lemma surface_vs_bulk_sdf_conservation_proved_false :
  surfaceVsBulkSdfConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_unwired false false =
  svbs_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_unwired false false =
  svbs_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_unwired false false) =
  true.
Proof.
  unfold svbs_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt78_witness_named_ok :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false false =
  svbs_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_surface_vs_bulk_sdf_conservation :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false false =
  svbs_verdict_named_ok /\
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfPt78Witness = true /\
  platinum_atomic_number_z = 78 /\
  pattern_class_surface_vs_bulk_sdf_idx = 9.
Proof.
  repeat split; reflexivity.
Qed.

Lemma svbs_named_close_ok :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_proved false false =
  svbs_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_surface_vs_bulk_sdf_conservation_close :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_proved false false =
  svbs_verdict_named_ok /\
  surface_vs_bulk_sdf_conservation_authorized false false = true.
Proof.
  split.
  - apply svbs_named_close_ok.
  - unfold surface_vs_bulk_sdf_conservation_authorized.
    rewrite svbs_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — surface-vs-bulk-sdf refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfEmptyWitness
    surfaceVsBulkSdfClaimBarAbsent false false false =
  svbs_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfEmptyWitness
    surfaceVsBulkSdfClaimBarAbsent false false false =
  svbs_verdict_trivial_refuse /\
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_bundle
       surface_vs_bulk_sdf_conservation_unwired
       surfaceVsBulkSdfEmptyWitness
       surfaceVsBulkSdfClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold svbs_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent true false false =
  svbs_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent true false false =
  svbs_verdict_xor_refuse /\
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_bundle
       surface_vs_bulk_sdf_conservation_unwired
       surfaceVsBulkSdfPt78Witness
       surfaceVsBulkSdfClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold svbs_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_unwired true false =
  svbs_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_unwired true false) =
  false.
Proof.
  unfold svbs_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_svbs_bundle_refuse :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false true false =
  svbs_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — surface-vs-bulk-sdf refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false true =
  svbs_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false true =
  svbs_verdict_proved_without_bar_refuse /\
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_bundle
       surface_vs_bulk_sdf_conservation_unwired
       surfaceVsBulkSdfPt78Witness
       surfaceVsBulkSdfClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold svbs_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — surface-vs-bulk-sdf lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_proved false true =
  svbs_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_proved false true) =
  false.
Proof.
  unfold svbs_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel surface-vs-bulk-sdf axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition surfaceVsBulkSdfConservationAuthority : string :=
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs".

Definition parallelSurfaceVsBulkSdfAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_surface_vs_bulk_sdf_axiom_refuse :
  surfaceVsBulkSdfConservationAuthority <>
  parallelSurfaceVsBulkSdfAxiomTag /\
  surfaceVsBulkSdfConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply surface_vs_bulk_sdf_conservation_proved_false.
Qed.

Theorem parallel_surface_vs_bulk_sdf_axiom_not_minted :
  surfaceVsBulkSdfConservationAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs" /\
  surfaceVsBulkSdfConservationProved = false /\
  surfaceVsBulkSdfConservationAuthority <> parallelSurfaceVsBulkSdfAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — geometry slice ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition surfaceVsBulkSdfConservationFraming : string :=
  "second_law_conservation_surface_vs_bulk_sdf_geometry_slice_one_axiom".

Lemma species_id_smuggle_refuse :
  surfaceVsBulkSdfConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_surface_vs_bulk_sdf_idx = 9.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem geometry_slice_not_species_id_smuggle :
  surfaceVsBulkSdfConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_surface_vs_bulk_sdf_idx = 9 /\
  surfaceVsBulkSdfConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — surface vs bulk sdf ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  surfaceVsBulkSdfConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  surfaceVsBulkSdfConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — surface vs bulk sdf ≠ CAT-03 adjunction    *)
(* ------------------------------------------------------------------ *)

Definition freePurificationFraming : string :=
  "free_purification_reverse_refine_cat03_adjunction".

Definition interactEngineClosedShellAuthority : string :=
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs".

Lemma free_purification_refuse :
  surfaceVsBulkSdfConservationFraming <>
  freePurificationFraming /\
  interactEngineClosedShellAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem surface_vs_bulk_sdf_not_free_purification :
  surfaceVsBulkSdfConservationFraming <>
  freePurificationFraming /\
  interactEngineClosedShellAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs" /\
  surfaceVsBulkSdfConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_surface_vs_bulk_sdf_scaffold".

Lemma tp_float_pin_refuse :
  surfaceVsBulkSdfConservationFraming <>
  tpFloatPinFraming /\
  geometry_slice_same_object_tag = "geometry_slice_same_object".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  surfaceVsBulkSdfConservationFraming <>
  tpFloatPinFraming /\
  catalysis_interact_restriction_tag = "catalysis_interact_restriction" /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Surface-vs-bulk-sdf **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition svbs_conservation_coherence_scaffold : bool :=
  svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_proved false false) &&
  negb (svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_unwired true false)) &&
  negb (svbs_conservation_verdict_ok
    (evaluate_surface_vs_bulk_sdf_conservation_close
       surface_vs_bulk_sdf_conservation_proved false true)).

Lemma svbs_conservation_coherence_scaffold_true :
  svbs_conservation_coherence_scaffold = true.
Proof.
  unfold svbs_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem svbs_conservation_coherence_scaffold_theorem :
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_proved false false =
    svbs_verdict_named_ok /\
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_unwired true false =
    svbs_verdict_green_invent_refuse /\
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_proved false true =
    svbs_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition svbs_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition svbs_conservation_knowing_fiber_ok : bool :=
  svbs_conservation_fiber_ok fiber_quantum_knowing.

Definition svbs_conservation_meso_acting_ok : bool :=
  svbs_conservation_fiber_ok fiber_meso_acting.

Lemma svbs_conservation_knowing_fiber_ok_true :
  svbs_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma svbs_conservation_meso_acting_not_ok :
  svbs_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem svbs_conservation_routes_knowing_not_meso :
  svbs_conservation_knowing_fiber_ok = true /\
  svbs_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply svbs_conservation_knowing_fiber_ok_true.
  - apply svbs_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  svbs_conservation_knowing_fiber_ok &&
  negb svbs_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, svbs_conservation_knowing_fiber_ok,
    svbs_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-15 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem surface_vs_bulk_sdf_conservation_fixture_scaffold :
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false false =
    svbs_verdict_named_ok /\
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfEmptyWitness
    surfaceVsBulkSdfClaimBarAbsent false false false =
    svbs_verdict_trivial_refuse /\
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent true false false =
    svbs_verdict_xor_refuse /\
  evaluate_surface_vs_bulk_sdf_bundle
    surface_vs_bulk_sdf_conservation_unwired
    surfaceVsBulkSdfPt78Witness
    surfaceVsBulkSdfClaimBarAbsent false false true =
    svbs_verdict_proved_without_bar_refuse /\
  evaluate_surface_vs_bulk_sdf_conservation_close
    surface_vs_bulk_sdf_conservation_unwired false false =
    svbs_verdict_unwired_ok /\
  svbs_conservation_knowing_fiber_ok = true /\
  svbs_conservation_meso_acting_ok = false /\
  surfaceVsBulkSdfConservationProved = false /\
  svbsProductNotXor = true /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — surface vs bulk sdf) *)
(* ------------------------------------------------------------------ *)

Definition chemL0SurfaceVsBulkSdfAuthority : string :=
  "umst/umst-chem/src/pattern_taxonomy.rs".

Definition chemL0SurfaceVsBulkSdfTableAuthority : string :=
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs".

Definition surfaceBulkGeometrySliceAuthority : string :=
  "umst/umst-chem/src/pattern_taxonomy.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0Graph02CellId : string := "CHEM-L0-GRAPH-02".

Definition surfaceVsBulkSdfConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-SURFACE-VS-BULK-SDF-CONSERVATION".

Definition surfaceVsBulkSdfConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-SURFACE-VS-BULK-SDF-CONSERVATION SurfaceVsBulkSdfConservationModality Unwired Assumed Proved Surrogate four-step lattice surfaceVsBulkSdfConservationProved false evaluateSurfaceVsBulkSdfBundle evaluateSurfaceVsBulkSdfConservation named class 15 surface_vs_bulk_sdf Pt Z=78 geometry slice same object catalysis Interact restriction concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel surface vs bulk sdf axiom refuse species id smuggle refuse extra element id Z=119 refuse free purification CAT-03 refuse surface vs bulk sdf ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma surface_vs_bulk_sdf_conservation_cell_id :
  surfaceVsBulkSdfConservationCellId =
  "CHEM-FORMAL-Q-COQ-SURFACE-VS-BULK-SDF-CONSERVATION".
Proof. reflexivity. Qed.

Lemma surface_vs_bulk_sdf_conservation_cites_l0_table :
  chemL0SurfaceVsBulkSdfTableAuthority <> "".
Proof. discriminate. Qed.

Lemma surface_vs_bulk_sdf_conservation_authority_path :
  surfaceVsBulkSdfConservationAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs".
Proof. reflexivity. Qed.

Lemma surface_vs_bulk_sdf_conservation_cites_l0_ore02 :
  chemL0SurfaceVsBulkSdfAuthority <> "".
Proof. discriminate. Qed.

Lemma surface_vs_bulk_sdf_conservation_cites_marker :
  svbsConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma surface_vs_bulk_sdf_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma surface_vs_bulk_sdf_conservation_cites_ore02_cell :
  chemL0Graph02CellId = "CHEM-L0-GRAPH-02".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma surface_vs_bulk_sdf_not_26th_axiom :
  surfaceVsBulkSdfConservationFraming <> parallelSurfaceVsBulkSdfAxiomTag.
Proof. discriminate. Qed.

Lemma surface_vs_bulk_sdf_second_law_conservation_framing :
  surfaceVsBulkSdfConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma surface_vs_bulk_sdf_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma surface_vs_bulk_sdf_conservation_modality_unwired :
  surfaceVsBulkSdfConservationModalityCurrent =
  surface_vs_bulk_sdf_conservation_unwired.
Proof. reflexivity. Qed.

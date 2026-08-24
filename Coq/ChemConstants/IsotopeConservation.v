(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: IsotopeConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 11 **isotope** **conservation**.            *)
(*  Electronic chemistry does not GREEN nuclear decay; isotope is a      *)
(*  concurrent PatternBundle Π_c factor — **product** not XOR. Not a    *)
(*  26th axiom; not a new ElementId. isotopeConservationProved false.   *)
(*  Modality Unwired. PatternProductConservation.v sibling.             *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/isotope.rs (read-only cite).       *)
(*  INT: umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs        *)
(*  (read-only cite).                                                    *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-11 **isotope** **conservation** modality                       *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive IsotopeConservationModality : Type :=
  | isotope_conservation_unwired
  | isotope_conservation_assumed
  | isotope_conservation_proved
  | isotope_conservation_surrogate.

Definition isotopeConservationModalityCurrent :
  IsotopeConservationModality :=
  isotope_conservation_unwired.

Definition isotope_lattice_cardinality : nat := 4.

Lemma isotope_lattice_cardinality_is_four :
  isotope_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma isotope_lattice_not_118_squared :
  negb (Nat.eqb isotope_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold isotope_lattice_cardinality.
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

(* North-star §2 class 11 — isotope concurrent Π_c factor. *)
Definition pattern_class_isotope_idx : nat := 11.

Lemma pattern_class_isotope_idx_is_11 :
  pattern_class_isotope_idx = 11.
Proof. reflexivity. Qed.

Lemma isotope_class_index_valid :
  pattern_class_index_valid pattern_class_isotope_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_isotope_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierIsotopeRowId : string := "X11".

Lemma cross_classifier_isotope_row_named :
  crossClassifierIsotopeRowId = "X11".
Proof. reflexivity. Qed.

Definition pattern_class_isotope_tag : string :=
  "isotope".

Definition north_star_class_11_isotope_tag : string :=
  "class 11 isotopes".

Lemma pattern_class_isotope_tag_nonempty :
  pattern_class_isotope_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_11_isotope_tag_nonempty :
  north_star_class_11_isotope_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Ar Z=18 CIAAW interval witness; U Z=92 nuclear      *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition argon_atomic_number_z : nat := 18.
Definition uranium_atomic_number_z : nat := 92.

Lemma argon_atomic_number_z_is_18 :
  argon_atomic_number_z = 18.
Proof. reflexivity. Qed.

Lemma uranium_atomic_number_z_is_92 :
  uranium_atomic_number_z = 92.
Proof. reflexivity. Qed.

Definition argon_z_valid : bool :=
  Nat.ltb 0 argon_atomic_number_z &&
  Nat.leb argon_atomic_number_z iupac_table_cardinality.

Lemma argon_z_valid_true : argon_z_valid = true.
Proof.
  unfold argon_z_valid, argon_atomic_number_z, iupac_table_cardinality.
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

Definition isotope_factor_tag : string :=
  "isotope".

Definition electronic_chem_channel_tag : string := "electronic_chemistry".

Definition nuclear_decay_channel_tag : string := "nuclear_decay_radioactivity".

Lemma isotope_factor_tag_nonempty :
  isotope_factor_tag <> "".
Proof. discriminate. Qed.

Lemma electronic_chem_channel_tag_nonempty :
  electronic_chem_channel_tag <> "".
Proof. discriminate. Qed.

Lemma nuclear_decay_channel_tag_nonempty :
  nuclear_decay_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope product channel — concurrent **product**                     *)
(* ------------------------------------------------------------------ *)

Inductive iso_channel_slot : Type :=
  | iso_slot_unwired
  | iso_slot_absent
  | iso_slot_present.

Definition iso_channel_slot_beq (s1 s2 : iso_channel_slot) : bool :=
  match s1, s2 with
  | iso_slot_unwired, iso_slot_unwired => true
  | iso_slot_absent, iso_slot_absent => true
  | iso_slot_present, iso_slot_present => true
  | _, _ => false
  end.

Definition iso_channel_slot_is_present (s : iso_channel_slot) : bool :=
  match s with
  | iso_slot_present => true
  | _ => false
  end.

Definition isotopeProductChannelCount : nat := 3.

Lemma isotope_product_channel_count_is_three :
  isotopeProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = electronic chem, 1 = nuclear decay, 2 = class 11. *)
Definition iso_channel_electronic_chem : nat := 0.
Definition iso_channel_nuclear_decay : nat := 1.
Definition iso_channel_class11_isotope : nat := 2.

Lemma iso_channel_electronic_chem_idx_is_0 :
  iso_channel_electronic_chem = 0.
Proof. reflexivity. Qed.

Lemma iso_channel_nuclear_decay_idx_is_1 :
  iso_channel_nuclear_decay = 1.
Proof. reflexivity. Qed.

Lemma iso_channel_class11_isotope_idx_is_2 :
  iso_channel_class11_isotope = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope concurrent **product** bundle scaffold                       *)
(* ------------------------------------------------------------------ *)

Definition iso_channel_bundle : Type := nat -> iso_channel_slot.

Definition isotopeBundleAllUnwired : iso_channel_bundle :=
  fun _ => iso_slot_unwired.

Definition isotopeBundleAt (b : iso_channel_bundle) (idx : nat)
  (slot : iso_channel_slot) : iso_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition isotopeBundleWithPresent
  (b : iso_channel_bundle) (idx : nat) : iso_channel_bundle :=
  isotopeBundleAt b idx iso_slot_present.

Fixpoint count_iso_present_up_to (b : iso_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if iso_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_iso_present_up_to b i + add
  end.

Definition isotopeBundlePresentCount (b : iso_channel_bundle) : nat :=
  count_iso_present_up_to b isotopeProductChannelCount.

Definition isotopeBundleHolds (b : iso_channel_bundle) (idx : nat) : bool :=
  iso_channel_slot_is_present (b idx).

Definition isotopeBundleIsConcurrentProduct (b : iso_channel_bundle) : bool :=
  Nat.leb 2 (isotopeBundlePresentCount b).

(* Ar Z=18 electronic + nuclear decay boundary + class-11 isotope concurrent witness. *)
Definition isotopeAr18Witness : iso_channel_bundle :=
  isotopeBundleWithPresent
    (isotopeBundleWithPresent
      (isotopeBundleWithPresent isotopeBundleAllUnwired
        iso_channel_electronic_chem)
      iso_channel_nuclear_decay)
    iso_channel_class11_isotope.

Definition isotopeEmptyWitness : iso_channel_bundle :=
  isotopeBundleAllUnwired.

Definition isotopeSinglePresent : iso_channel_bundle :=
  isotopeBundleWithPresent isotopeBundleAllUnwired
    iso_channel_electronic_chem.

Lemma electronic_chem_channel_present :
  isotopeBundleHolds isotopeAr18Witness
    iso_channel_electronic_chem = true.
Proof. reflexivity. Qed.

Lemma nuclear_decay_channel_present :
  isotopeBundleHolds isotopeAr18Witness
    iso_channel_nuclear_decay = true.
Proof. reflexivity. Qed.

Lemma class11_isotope_channel_present :
  isotopeBundleHolds isotopeAr18Witness
    iso_channel_class11_isotope = true.
Proof. reflexivity. Qed.

Lemma ar18_witness_present_count_is_three :
  isotopeBundlePresentCount isotopeAr18Witness = 3.
Proof. reflexivity. Qed.

Lemma ar18_witness_is_concurrent_product :
  isotopeBundleIsConcurrentProduct isotopeAr18Witness = true.
Proof.
  unfold isotopeBundleIsConcurrentProduct.
  rewrite ar18_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  isotopeBundlePresentCount isotopeEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  isotopeBundleIsConcurrentProduct isotopeEmptyWitness = false.
Proof.
  unfold isotopeBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  isotopeBundlePresentCount isotopeSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  isotopeBundleIsConcurrentProduct isotopeSinglePresent = false.
Proof.
  unfold isotopeBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive iso_xor_posture : Type :=
  | iso_xor_exclusive
  | iso_xor_concurrent_product.

Definition isoXorClassifierMarker : string := "chem_l0_isotope_xor_classifier_v1".
Definition isoConcurrentProductMarker : string := "chem_int_isotope_product_v1".

Lemma iso_xor_marker_ne_concurrent_product_marker :
  isoXorClassifierMarker <> isoConcurrentProductMarker.
Proof. discriminate. Qed.

Definition isoXorClassifierIncompatible (claim_xor : bool)
  (b : iso_channel_bundle) : bool :=
  claim_xor && isotopeBundleIsConcurrentProduct b.

Lemma iso_xor_refuse_on_ar18_witness :
  isoXorClassifierIncompatible true isotopeAr18Witness = true.
Proof.
  unfold isoXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma iso_xor_ok_on_concurrent_product_claim :
  isoXorClassifierIncompatible false isotopeAr18Witness = false.
Proof. reflexivity. Qed.

Definition isoProductNotXor : bool :=
  isotopeBundleIsConcurrentProduct isotopeAr18Witness &&
  isoXorClassifierIncompatible true isotopeAr18Witness.

Lemma iso_product_not_xor_true : isoProductNotXor = true.
Proof.
  unfold isoProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  isoProductNotXor = true /\
  Nat.leb 2 (isotopeBundlePresentCount
    isotopeAr18Witness) = true /\
  isoXorClassifierMarker <> isoConcurrentProductMarker.
Proof.
  split.
  - apply iso_product_not_xor_true.
  - split.
    + rewrite ar18_witness_present_count_is_three.
      reflexivity.
    + apply iso_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** bar — Proved-without-bar fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive iso_bar_presence : Type :=
  | iso_bar_absent
  | iso_bar_present.

Record iso_claim_bar : Type := {
  iso_bar_presence_field : iso_bar_presence;
  iso_bar_defect_total : nat
}.

Definition isotopeClaimBarAbsent : iso_claim_bar :=
  {| iso_bar_presence_field := iso_bar_absent;
     iso_bar_defect_total := 0 |}.

Definition isotopeClaimBarZeroDefect : iso_claim_bar :=
  {| iso_bar_presence_field := iso_bar_present;
     iso_bar_defect_total := 0 |}.

Definition iso_claim_bar_zero_defect (b : iso_claim_bar) : bool :=
  match iso_bar_presence_field b with
  | iso_bar_absent => false
  | iso_bar_present => Nat.eqb (iso_bar_defect_total b) 0
  end.

Lemma iso_claim_bar_zero_defect_true :
  iso_claim_bar_zero_defect isotopeClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma iso_claim_bar_absent_not_zero_defect :
  iso_claim_bar_zero_defect isotopeClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** verdict — fail-closed lattice              *)
(* ------------------------------------------------------------------ *)

Inductive iso_conservation_verdict : Type :=
  | iso_verdict_unwired_ok
  | iso_verdict_named_ok
  | iso_verdict_design_ok
  | iso_verdict_trivial_refuse
  | iso_verdict_xor_refuse
  | iso_verdict_green_invent_refuse
  | iso_verdict_proved_without_bar_refuse
  | iso_verdict_production_wired_refuse
  | iso_verdict_parallel_isotope_axiom_refuse
  | iso_verdict_species_id_smuggle_refuse
  | iso_verdict_extra_element_id_refuse
  | iso_verdict_nuclear_decay_chem_green_refuse
  | iso_verdict_tp_float_pin_refuse.

Definition iso_conservation_verdict_ok (v : iso_conservation_verdict) : bool :=
  match v with
  | iso_verdict_unwired_ok => true
  | iso_verdict_named_ok => true
  | iso_verdict_design_ok => true
  | _ => false
  end.

Definition isotopeBundleNontrivial (b : iso_channel_bundle) : bool :=
  Nat.ltb 0 (isotopeBundlePresentCount b).

Definition evaluate_isotope_bundle
  (m : IsotopeConservationModality)
  (b : iso_channel_bundle)
  (bar : iso_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_nuclear_decay_chem_green : bool) : iso_conservation_verdict :=
  if claim_physics_green
  then iso_verdict_green_invent_refuse
  else if claim_nuclear_decay_chem_green
       then iso_verdict_nuclear_decay_chem_green_refuse
       else if claim_proved
            then iso_verdict_proved_without_bar_refuse
            else if negb (isotopeBundleNontrivial b)
                 then iso_verdict_trivial_refuse
                 else if isoXorClassifierIncompatible claim_xor_classifier b
                      then iso_verdict_xor_refuse
                      else
                        match m with
                        | isotope_conservation_unwired =>
                            if isotopeBundleIsConcurrentProduct b
                            then iso_verdict_named_ok
                            else iso_verdict_design_ok
                        | isotope_conservation_assumed
                        | isotope_conservation_surrogate =>
                            iso_verdict_design_ok
                        | isotope_conservation_proved =>
                            iso_verdict_proved_without_bar_refuse
                        end.

Definition evaluate_isotope_conservation_close
  (m : IsotopeConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : iso_conservation_verdict :=
  if claim_physics_green
  then iso_verdict_green_invent_refuse
  else if claim_production_wired
  then iso_verdict_production_wired_refuse
  else
    match m with
    | isotope_conservation_unwired => iso_verdict_unwired_ok
    | isotope_conservation_assumed
    | isotope_conservation_proved
    | isotope_conservation_surrogate => iso_verdict_named_ok
    end.

Definition isotope_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_isotope_conservation_close
          isotope_conservation_proved claim_physics_green claim_production_wired with
  | iso_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** law cells — four laws                      *)
(* ------------------------------------------------------------------ *)

Inductive iso_conservation_law : Type :=
  | iso_law_conserved
  | iso_law_named_ok
  | iso_law_trivial_refuse
  | iso_law_green_invent_refuse.

Definition iso_conservation_law_count : nat := 4.

Lemma iso_conservation_law_count_is_four :
  iso_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive iso_conservation_law_witness : Type :=
  | iso_law_witness_open
  | iso_law_witness_proved.

Definition evaluate_iso_conservation_law_witness
  (law : iso_conservation_law)
  (m : IsotopeConservationModality)
  : iso_conservation_law_witness :=
  match m with
  | isotope_conservation_unwired
  | isotope_conservation_assumed
  | isotope_conservation_surrogate => iso_law_witness_open
  | isotope_conservation_proved => iso_law_witness_proved
  end.

Lemma all_iso_conservation_laws_open_at_unwired :
  evaluate_iso_conservation_law_witness iso_law_conserved
    isotope_conservation_unwired = iso_law_witness_open /\
  evaluate_iso_conservation_law_witness iso_law_named_ok
    isotope_conservation_unwired = iso_law_witness_open /\
  evaluate_iso_conservation_law_witness iso_law_trivial_refuse
    isotope_conservation_unwired = iso_law_witness_open /\
  evaluate_iso_conservation_law_witness iso_law_green_invent_refuse
    isotope_conservation_unwired = iso_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-11 pins (structure witnesses — conservation laws not Proved)  *)
(* ------------------------------------------------------------------ *)

Definition isotopeConservationProved : bool := false.

Lemma isotope_conservation_proved_false :
  isotopeConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_isotope_conservation_close
    isotope_conservation_unwired false false =
  iso_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_isotope_conservation_close
    isotope_conservation_unwired false false =
  iso_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_unwired false false) =
  true.
Proof.
  unfold iso_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Ar Z=18 close — concurrent **product**                         *)
(* ------------------------------------------------------------------ *)

Lemma ar18_witness_named_ok :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false false =
  iso_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ar18_isotope_conservation :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false false =
  iso_verdict_named_ok /\
  isotopeBundleIsConcurrentProduct isotopeAr18Witness = true /\
  argon_atomic_number_z = 18 /\
  pattern_class_isotope_idx = 11.
Proof.
  repeat split; reflexivity.
Qed.

Lemma iso_named_close_ok :
  evaluate_isotope_conservation_close
    isotope_conservation_proved false false =
  iso_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_isotope_conservation_close :
  evaluate_isotope_conservation_close
    isotope_conservation_proved false false =
  iso_verdict_named_ok /\
  isotope_conservation_authorized false false = true.
Proof.
  split.
  - apply iso_named_close_ok.
  - unfold isotope_conservation_authorized.
    rewrite iso_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — isotope refuse                   *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeEmptyWitness
    isotopeClaimBarAbsent false false false false =
  iso_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeEmptyWitness
    isotopeClaimBarAbsent false false false false =
  iso_verdict_trivial_refuse /\
  iso_conservation_verdict_ok
    (evaluate_isotope_bundle
       isotope_conservation_unwired
       isotopeEmptyWitness
       isotopeClaimBarAbsent false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold iso_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent true false false false =
  iso_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent true false false false =
  iso_verdict_xor_refuse /\
  iso_conservation_verdict_ok
    (evaluate_isotope_bundle
       isotope_conservation_unwired
       isotopeAr18Witness
       isotopeClaimBarAbsent true false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold iso_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_isotope_conservation_close
    isotope_conservation_unwired true false =
  iso_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_unwired true false) =
  false.
Proof.
  unfold iso_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_iso_bundle_refuse :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false true false false =
  iso_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Nuclear decay ≠ electronic chem GREEN — fail-closed                 *)
(* ------------------------------------------------------------------ *)

Lemma nuclear_decay_chem_green_refuse :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false true =
  iso_verdict_nuclear_decay_chem_green_refuse.
Proof. reflexivity. Qed.

Theorem nuclear_decay_not_chem_green_fail_closed :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false true =
  iso_verdict_nuclear_decay_chem_green_refuse /\
  iso_conservation_verdict_ok
    (evaluate_isotope_bundle
       isotope_conservation_unwired
       isotopeAr18Witness
       isotopeClaimBarAbsent false false false true) =
  false.
Proof.
  split.
  - apply nuclear_decay_chem_green_refuse.
  - unfold iso_conservation_verdict_ok.
    rewrite nuclear_decay_chem_green_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — isotope refuse                       *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false true false =
  iso_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false true false =
  iso_verdict_proved_without_bar_refuse /\
  iso_conservation_verdict_ok
    (evaluate_isotope_bundle
       isotope_conservation_unwired
       isotopeAr18Witness
       isotopeClaimBarAbsent false false true false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold iso_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — isotope lattice not wired                   *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_isotope_conservation_close
    isotope_conservation_proved false true =
  iso_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_proved false true) =
  false.
Proof.
  unfold iso_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel isotope axiom refuse — morphism not 26th axiom               *)
(* ------------------------------------------------------------------ *)

Definition isotopeConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/isotope.rs".

Definition parallelIsotopeAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_isotope_axiom_refuse :
  isotopeConservationAuthority <>
  parallelIsotopeAxiomTag /\
  isotopeConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply isotope_conservation_proved_false.
Qed.

Theorem parallel_isotope_axiom_not_minted :
  isotopeConservationAuthority =
  "umst/umst-chem/src/l0_tables/isotope.rs" /\
  isotopeConservationProved = false /\
  isotopeConservationAuthority <> parallelIsotopeAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — isotope ≠ L1 SpeciesId occupancy tag       *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition isotopeConservationFraming : string :=
  "second_law_conservation_isotope_one_axiom".

Lemma species_id_smuggle_refuse :
  isotopeConservationFraming <>
  speciesIdSmuggleFraming /\
  argon_atomic_number_z = 18 /\
  pattern_class_isotope_idx = 11.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem isotope_not_species_id_smuggle :
  isotopeConservationFraming <>
  speciesIdSmuggleFraming /\
  argon_atomic_number_z = 18 /\
  pattern_class_isotope_idx = 11 /\
  isotopeConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — isotope ≠ Z=119 smuggle                      *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  isotopeConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem isotope_not_extra_element_id :
  isotopeConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  argon_atomic_number_z = 18.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins          *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_isotope_scaffold".

Lemma tp_float_pin_refuse :
  isotopeConservationFraming <>
  tpFloatPinFraming /\
  nuclear_decay_channel_tag = "nuclear_decay_radioactivity".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  isotopeConservationFraming <>
  tpFloatPinFraming /\
  electronic_chem_channel_tag = "electronic_chemistry" /\
  argon_atomic_number_z = 18.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** coherence scaffold                           *)
(* ------------------------------------------------------------------ *)

Definition iso_conservation_coherence_scaffold : bool :=
  iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_proved false false) &&
  negb (iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_unwired true false)) &&
  negb (iso_conservation_verdict_ok
    (evaluate_isotope_conservation_close
       isotope_conservation_proved false true)).

Lemma iso_conservation_coherence_scaffold_true :
  iso_conservation_coherence_scaffold = true.
Proof.
  unfold iso_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem iso_conservation_coherence_scaffold_theorem :
  evaluate_isotope_conservation_close
    isotope_conservation_proved false false =
    iso_verdict_named_ok /\
  evaluate_isotope_conservation_close
    isotope_conservation_unwired true false =
    iso_verdict_green_invent_refuse /\
  evaluate_isotope_conservation_close
    isotope_conservation_proved false true =
    iso_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting            *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition iso_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition iso_conservation_knowing_fiber_ok : bool :=
  iso_conservation_fiber_ok fiber_quantum_knowing.

Definition iso_conservation_meso_acting_ok : bool :=
  iso_conservation_fiber_ok fiber_meso_acting.

Lemma iso_conservation_knowing_fiber_ok_true :
  iso_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma iso_conservation_meso_acting_not_ok :
  iso_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem iso_conservation_routes_knowing_not_meso :
  iso_conservation_knowing_fiber_ok = true /\
  iso_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply iso_conservation_knowing_fiber_ok_true.
  - apply iso_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  iso_conservation_knowing_fiber_ok &&
  negb iso_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, iso_conservation_knowing_fiber_ok,
    iso_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-11 + fail-closed + fiber               *)
(* ------------------------------------------------------------------ *)

Theorem isotope_conservation_fixture_scaffold :
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false false =
    iso_verdict_named_ok /\
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeEmptyWitness
    isotopeClaimBarAbsent false false false false =
    iso_verdict_trivial_refuse /\
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent true false false false =
    iso_verdict_xor_refuse /\
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false true false =
    iso_verdict_proved_without_bar_refuse /\
  evaluate_isotope_bundle
    isotope_conservation_unwired
    isotopeAr18Witness
    isotopeClaimBarAbsent false false false true =
    iso_verdict_nuclear_decay_chem_green_refuse /\
  evaluate_isotope_conservation_close
    isotope_conservation_unwired false false =
    iso_verdict_unwired_ok /\
  iso_conservation_knowing_fiber_ok = true /\
  iso_conservation_meso_acting_ok = false /\
  isotopeConservationProved = false /\
  isoProductNotXor = true /\
  argon_atomic_number_z = 18.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — isotope)             *)
(* ------------------------------------------------------------------ *)

Definition chemL0IsotopeTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/isotope.rs".

Definition isotopeBoundaryAuthority : string :=
  "umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeIsotopeCellId : string := "CHEM-L0-EDGE-ISOTOPE".

Definition chemIntNuanceIsotopeCellId : string := "CHEM-INT-NUANCE-ISOTOPE".

Definition isotopeConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ISOTOPE-CONSERVATION".

Definition isotopeConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ISOTOPE-CONSERVATION IsotopeConservationModality Unwired Assumed Proved Surrogate four-step lattice isotopeConservationProved false evaluateIsotopeBundle evaluateIsotopeConservation named class 11 isotope Ar Z=18 electronic chemistry nuclear decay radioactivity concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel isotope axiom refuse species id smuggle refuse extra element id Z=119 refuse nuclear decay chem GREEN refuse isotope ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma isotope_conservation_cell_id :
  isotopeConservationCellId =
  "CHEM-FORMAL-Q-COQ-ISOTOPE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma isotope_conservation_cites_l0_table :
  chemL0IsotopeTableAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_conservation_authority_path :
  isotopeConservationAuthority =
  "umst/umst-chem/src/l0_tables/isotope.rs".
Proof. reflexivity. Qed.

Lemma isotope_conservation_cites_boundary :
  isotopeBoundaryAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_conservation_cites_marker :
  isoConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma isotope_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_conservation_cites_edge_cell :
  chemL0EdgeIsotopeCellId = "CHEM-L0-EDGE-ISOTOPE".
Proof. reflexivity. Qed.

Lemma isotope_conservation_cites_nuance_cell :
  chemIntNuanceIsotopeCellId = "CHEM-INT-NUANCE-ISOTOPE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom     *)
(* ------------------------------------------------------------------ *)

Lemma isotope_not_26th_axiom :
  isotopeConservationFraming <> parallelIsotopeAxiomTag.
Proof. discriminate. Qed.

Lemma isotope_second_law_conservation_framing :
  isotopeConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma isotope_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma isotope_conservation_modality_unwired :
  isotopeConservationModalityCurrent =
  isotope_conservation_unwired.
Proof. reflexivity. Qed.

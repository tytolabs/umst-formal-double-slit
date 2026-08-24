(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: IsotopeNuclearBoundaryConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 11 **isotope nuclear boundary** **conservation**.         *)
(*  Electronic occupancy does not certify nuclear decay; isotope is a *)
(*  concurrent PatternBundle Π_c factor — **product** not XOR. Not a    *)
(*  119th ElementId; not a 26th axiom. isotopeNuclearBoundaryConservationProved false. *)
(*  Modality Unwired. IsotopeConservation.v sibling.                    *)
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
(*  Class-11 **isotope nuclear boundary** **conservation** modality                       *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive IsotopeNuclearBoundaryConservationModality : Type :=
  | isotope_nuclear_boundary_conservation_unwired
  | isotope_nuclear_boundary_conservation_assumed
  | isotope_nuclear_boundary_conservation_proved
  | isotope_nuclear_boundary_conservation_surrogate.

Definition isotopeNuclearBoundaryConservationModalityCurrent :
  IsotopeNuclearBoundaryConservationModality :=
  isotope_nuclear_boundary_conservation_unwired.

Definition inb_lattice_cardinality : nat := 4.

Lemma inb_lattice_cardinality_is_four :
  inb_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma inb_lattice_not_118_squared :
  negb (Nat.eqb inb_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold inb_lattice_cardinality.
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

(* North-star §2 class 11 — isotope nuclear boundary concurrent Π_c factor. *)
Definition pattern_class_inb_idx : nat := 11.

Lemma pattern_class_inb_idx_is_11 :
  pattern_class_inb_idx = 11.
Proof. reflexivity. Qed.

Lemma inb_class_index_valid :
  pattern_class_index_valid pattern_class_inb_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_inb_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierInbRowId : string := "X11".

Lemma cross_classifier_isotope_row_named :
  crossClassifierInbRowId = "X11".
Proof. reflexivity. Qed.

Definition pattern_class_inb_tag : string :=
  "isotope_nuclear_boundary".

Definition north_star_class_11_inb_tag : string :=
  "class 11 isotope nuclear boundarys".

Lemma pattern_class_inb_tag_nonempty :
  pattern_class_inb_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_11_inb_tag_nonempty :
  north_star_class_11_inb_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Pm Z=61 CIAAW interval witness; U Z=92 nuclear      *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition promethium_atomic_number_z : nat := 61.
Definition uranium_atomic_number_z : nat := 92.

Lemma promethium_atomic_number_z_is_18 :
  promethium_atomic_number_z = 61.
Proof. reflexivity. Qed.

Lemma uranium_atomic_number_z_is_92 :
  uranium_atomic_number_z = 92.
Proof. reflexivity. Qed.

Definition promethium_z_valid : bool :=
  Nat.ltb 0 promethium_atomic_number_z &&
  Nat.leb promethium_atomic_number_z iupac_table_cardinality.

Lemma promethium_z_valid_true : promethium_z_valid = true.
Proof.
  unfold promethium_z_valid, promethium_atomic_number_z, iupac_table_cardinality.
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

Definition inb_factor_tag : string :=
  "isotope_nuclear_boundary".

Definition electronic_chem_channel_tag : string := "electronic_occupancy".

Definition nuclear_decay_channel_tag : string := "nuclear_decay_boundary".

Lemma inb_factor_tag_nonempty :
  inb_factor_tag <> "".
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

Inductive inb_channel_slot : Type :=
  | inb_slot_unwired
  | inb_slot_absent
  | inb_slot_present.

Definition inb_channel_slot_beq (s1 s2 : inb_channel_slot) : bool :=
  match s1, s2 with
  | inb_slot_unwired, inb_slot_unwired => true
  | inb_slot_absent, inb_slot_absent => true
  | inb_slot_present, inb_slot_present => true
  | _, _ => false
  end.

Definition inb_channel_slot_is_present (s : inb_channel_slot) : bool :=
  match s with
  | inb_slot_present => true
  | _ => false
  end.

Definition inbProductChannelCount : nat := 3.

Lemma isotope_product_channel_count_is_three :
  inbProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = electronic chem, 1 = nuclear decay, 2 = class 11. *)
Definition inb_channel_electronic_chem : nat := 0.
Definition inb_channel_nuclear_decay : nat := 1.
Definition inb_channel_class11_isotope : nat := 2.

Lemma inb_channel_electronic_chem_idx_is_0 :
  inb_channel_electronic_chem = 0.
Proof. reflexivity. Qed.

Lemma inb_channel_nuclear_decay_idx_is_1 :
  inb_channel_nuclear_decay = 1.
Proof. reflexivity. Qed.

Lemma inb_channel_class11_isotope_idx_is_2 :
  inb_channel_class11_isotope = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope concurrent **product** bundle scaffold                       *)
(* ------------------------------------------------------------------ *)

Definition inb_channel_bundle : Type := nat -> inb_channel_slot.

Definition inbBundleAllUnwired : inb_channel_bundle :=
  fun _ => inb_slot_unwired.

Definition inbBundleAt (b : inb_channel_bundle) (idx : nat)
  (slot : inb_channel_slot) : inb_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition inbBundleWithPresent
  (b : inb_channel_bundle) (idx : nat) : inb_channel_bundle :=
  inbBundleAt b idx inb_slot_present.

Fixpoint count_inb_present_up_to (b : inb_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if inb_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_inb_present_up_to b i + add
  end.

Definition inbBundlePresentCount (b : inb_channel_bundle) : nat :=
  count_inb_present_up_to b inbProductChannelCount.

Definition inbBundleHolds (b : inb_channel_bundle) (idx : nat) : bool :=
  inb_channel_slot_is_present (b idx).

Definition inbBundleIsConcurrentProduct (b : inb_channel_bundle) : bool :=
  Nat.leb 2 (inbBundlePresentCount b).

(* Pm Z=61 electronic + nuclear decay boundary + class-11 isotope nuclear boundary concurrent witness. *)
Definition inbPm61Witness : inb_channel_bundle :=
  inbBundleWithPresent
    (inbBundleWithPresent
      (inbBundleWithPresent inbBundleAllUnwired
        inb_channel_electronic_chem)
      inb_channel_nuclear_decay)
    inb_channel_class11_isotope.

Definition inbEmptyWitness : inb_channel_bundle :=
  inbBundleAllUnwired.

Definition inbSinglePresent : inb_channel_bundle :=
  inbBundleWithPresent inbBundleAllUnwired
    inb_channel_electronic_chem.

Lemma electronic_chem_channel_present :
  inbBundleHolds inbPm61Witness
    inb_channel_electronic_chem = true.
Proof. reflexivity. Qed.

Lemma nuclear_decay_channel_present :
  inbBundleHolds inbPm61Witness
    inb_channel_nuclear_decay = true.
Proof. reflexivity. Qed.

Lemma class11_inb_channel_present :
  inbBundleHolds inbPm61Witness
    inb_channel_class11_isotope = true.
Proof. reflexivity. Qed.

Lemma pm61_witness_present_count_is_three :
  inbBundlePresentCount inbPm61Witness = 3.
Proof. reflexivity. Qed.

Lemma pm61_witness_is_concurrent_product :
  inbBundleIsConcurrentProduct inbPm61Witness = true.
Proof.
  unfold inbBundleIsConcurrentProduct.
  rewrite pm61_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  inbBundlePresentCount inbEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  inbBundleIsConcurrentProduct inbEmptyWitness = false.
Proof.
  unfold inbBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  inbBundlePresentCount inbSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  inbBundleIsConcurrentProduct inbSinglePresent = false.
Proof.
  unfold inbBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive inb_xor_posture : Type :=
  | inb_xor_exclusive
  | inb_xor_concurrent_product.

Definition inbXorClassifierMarker : string := "chem_l0_inb_xor_classifier_v1".
Definition inbConcurrentProductMarker : string := "chem_int_inb_product_v1".

Lemma inb_xor_marker_ne_concurrent_product_marker :
  inbXorClassifierMarker <> inbConcurrentProductMarker.
Proof. discriminate. Qed.

Definition inbXorClassifierIncompatible (claim_xor : bool)
  (b : inb_channel_bundle) : bool :=
  claim_xor && inbBundleIsConcurrentProduct b.

Lemma inb_xor_refuse_on_pm61_witness :
  inbXorClassifierIncompatible true inbPm61Witness = true.
Proof.
  unfold inbXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma inb_xor_ok_on_concurrent_product_claim :
  inbXorClassifierIncompatible false inbPm61Witness = false.
Proof. reflexivity. Qed.

Definition inbProductNotXor : bool :=
  inbBundleIsConcurrentProduct inbPm61Witness &&
  inbXorClassifierIncompatible true inbPm61Witness.

Lemma inb_product_not_xor_true : inbProductNotXor = true.
Proof.
  unfold inbProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  inbProductNotXor = true /\
  Nat.leb 2 (inbBundlePresentCount
    inbPm61Witness) = true /\
  inbXorClassifierMarker <> inbConcurrentProductMarker.
Proof.
  split.
  - apply inb_product_not_xor_true.
  - split.
    + rewrite pm61_witness_present_count_is_three.
      reflexivity.
    + apply inb_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** bar — Proved-without-bar fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive inb_bar_presence : Type :=
  | inb_bar_absent
  | inb_bar_present.

Record inb_claim_bar : Type := {
  inb_bar_presence_field : inb_bar_presence;
  inb_bar_defect_total : nat
}.

Definition inbClaimBarAbsent : inb_claim_bar :=
  {| inb_bar_presence_field := inb_bar_absent;
     inb_bar_defect_total := 0 |}.

Definition inbClaimBarZeroDefect : inb_claim_bar :=
  {| inb_bar_presence_field := inb_bar_present;
     inb_bar_defect_total := 0 |}.

Definition inb_claim_bar_zero_defect (b : inb_claim_bar) : bool :=
  match inb_bar_presence_field b with
  | inb_bar_absent => false
  | inb_bar_present => Nat.eqb (inb_bar_defect_total b) 0
  end.

Lemma inb_claim_bar_zero_defect_true :
  inb_claim_bar_zero_defect inbClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma inb_claim_bar_absent_not_zero_defect :
  inb_claim_bar_zero_defect inbClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** verdict — fail-closed lattice              *)
(* ------------------------------------------------------------------ *)

Inductive inb_conservation_verdict : Type :=
  | inb_verdict_unwired_ok
  | inb_verdict_named_ok
  | inb_verdict_design_ok
  | inb_verdict_trivial_refuse
  | inb_verdict_xor_refuse
  | inb_verdict_green_invent_refuse
  | inb_verdict_proved_without_bar_refuse
  | inb_verdict_production_wired_refuse
  | inb_verdict_parallel_inb_axiom_refuse
  | inb_verdict_species_id_smuggle_refuse
  | inb_verdict_extra_element_id_refuse
  | inb_verdict_electronic_occupancy_certifies_nuclear_decay_refuse
  | inb_verdict_tp_float_pin_refuse.

Definition inb_conservation_verdict_ok (v : inb_conservation_verdict) : bool :=
  match v with
  | inb_verdict_unwired_ok => true
  | inb_verdict_named_ok => true
  | inb_verdict_design_ok => true
  | _ => false
  end.

Definition inbBundleNontrivial (b : inb_channel_bundle) : bool :=
  Nat.ltb 0 (inbBundlePresentCount b).

Definition evaluate_inb_bundle
  (m : IsotopeNuclearBoundaryConservationModality)
  (b : inb_channel_bundle)
  (bar : inb_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_electronic_occupancy_certifies_nuclear_decay : bool) : inb_conservation_verdict :=
  if claim_physics_green
  then inb_verdict_green_invent_refuse
  else if claim_electronic_occupancy_certifies_nuclear_decay
       then inb_verdict_electronic_occupancy_certifies_nuclear_decay_refuse
       else if claim_proved
            then inb_verdict_proved_without_bar_refuse
            else if negb (inbBundleNontrivial b)
                 then inb_verdict_trivial_refuse
                 else if inbXorClassifierIncompatible claim_xor_classifier b
                      then inb_verdict_xor_refuse
                      else
                        match m with
                        | isotope_nuclear_boundary_conservation_unwired =>
                            if inbBundleIsConcurrentProduct b
                            then inb_verdict_named_ok
                            else inb_verdict_design_ok
                        | isotope_nuclear_boundary_conservation_assumed
                        | isotope_nuclear_boundary_conservation_surrogate =>
                            inb_verdict_design_ok
                        | isotope_nuclear_boundary_conservation_proved =>
                            inb_verdict_proved_without_bar_refuse
                        end.

Definition evaluate_isotope_nuclear_boundary_conservation_close
  (m : IsotopeNuclearBoundaryConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : inb_conservation_verdict :=
  if claim_physics_green
  then inb_verdict_green_invent_refuse
  else if claim_production_wired
  then inb_verdict_production_wired_refuse
  else
    match m with
    | isotope_nuclear_boundary_conservation_unwired => inb_verdict_unwired_ok
    | isotope_nuclear_boundary_conservation_assumed
    | isotope_nuclear_boundary_conservation_proved
    | isotope_nuclear_boundary_conservation_surrogate => inb_verdict_named_ok
    end.

Definition isotope_nuclear_boundary_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_isotope_nuclear_boundary_conservation_close
          isotope_nuclear_boundary_conservation_proved claim_physics_green claim_production_wired with
  | inb_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** law cells — four laws                      *)
(* ------------------------------------------------------------------ *)

Inductive inb_conservation_law : Type :=
  | inb_law_conserved
  | inb_law_named_ok
  | inb_law_trivial_refuse
  | inb_law_green_invent_refuse.

Definition inb_conservation_law_count : nat := 4.

Lemma inb_conservation_law_count_is_four :
  inb_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive inb_conservation_law_witness : Type :=
  | inb_law_witness_open
  | inb_law_witness_proved.

Definition evaluate_inb_conservation_law_witness
  (law : inb_conservation_law)
  (m : IsotopeNuclearBoundaryConservationModality)
  : inb_conservation_law_witness :=
  match m with
  | isotope_nuclear_boundary_conservation_unwired
  | isotope_nuclear_boundary_conservation_assumed
  | isotope_nuclear_boundary_conservation_surrogate => inb_law_witness_open
  | isotope_nuclear_boundary_conservation_proved => inb_law_witness_proved
  end.

Lemma all_inb_conservation_laws_open_at_unwired :
  evaluate_inb_conservation_law_witness inb_law_conserved
    isotope_nuclear_boundary_conservation_unwired = inb_law_witness_open /\
  evaluate_inb_conservation_law_witness inb_law_named_ok
    isotope_nuclear_boundary_conservation_unwired = inb_law_witness_open /\
  evaluate_inb_conservation_law_witness inb_law_trivial_refuse
    isotope_nuclear_boundary_conservation_unwired = inb_law_witness_open /\
  evaluate_inb_conservation_law_witness inb_law_green_invent_refuse
    isotope_nuclear_boundary_conservation_unwired = inb_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-11 pins (structure witnesses — conservation laws not Proved)  *)
(* ------------------------------------------------------------------ *)

Definition isotopeNuclearBoundaryConservationProved : bool := false.

Lemma isotope_nuclear_boundary_conservation_proved_false :
  isotopeNuclearBoundaryConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_unwired false false =
  inb_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_unwired false false =
  inb_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_unwired false false) =
  true.
Proof.
  unfold inb_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pm Z=61 close — concurrent **product**                         *)
(* ------------------------------------------------------------------ *)

Lemma pm61_witness_named_ok :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false false =
  inb_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ar18_isotope_nuclear_boundary_conservation :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false false =
  inb_verdict_named_ok /\
  inbBundleIsConcurrentProduct inbPm61Witness = true /\
  promethium_atomic_number_z = 61 /\
  pattern_class_inb_idx = 11.
Proof.
  repeat split; reflexivity.
Qed.

Lemma inb_named_close_ok :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_proved false false =
  inb_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_isotope_nuclear_boundary_conservation_close :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_proved false false =
  inb_verdict_named_ok /\
  isotope_nuclear_boundary_conservation_authorized false false = true.
Proof.
  split.
  - apply inb_named_close_ok.
  - unfold isotope_nuclear_boundary_conservation_authorized.
    rewrite inb_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — isotope nuclear boundary refuse                   *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbEmptyWitness
    inbClaimBarAbsent false false false false =
  inb_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbEmptyWitness
    inbClaimBarAbsent false false false false =
  inb_verdict_trivial_refuse /\
  inb_conservation_verdict_ok
    (evaluate_inb_bundle
       isotope_nuclear_boundary_conservation_unwired
       inbEmptyWitness
       inbClaimBarAbsent false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold inb_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent true false false false =
  inb_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent true false false false =
  inb_verdict_xor_refuse /\
  inb_conservation_verdict_ok
    (evaluate_inb_bundle
       isotope_nuclear_boundary_conservation_unwired
       inbPm61Witness
       inbClaimBarAbsent true false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold inb_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_unwired true false =
  inb_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_unwired true false) =
  false.
Proof.
  unfold inb_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_inb_bundle_refuse :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false true false false =
  inb_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Electronic occupancy does not certify nuclear decay — fail-closed                 *)
(* ------------------------------------------------------------------ *)

Lemma electronic_occupancy_certifies_nuclear_decay_refuse :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false true =
  inb_verdict_electronic_occupancy_certifies_nuclear_decay_refuse.
Proof. reflexivity. Qed.

Theorem nuclear_decay_not_chem_green_fail_closed :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false true =
  inb_verdict_electronic_occupancy_certifies_nuclear_decay_refuse /\
  inb_conservation_verdict_ok
    (evaluate_inb_bundle
       isotope_nuclear_boundary_conservation_unwired
       inbPm61Witness
       inbClaimBarAbsent false false false true) =
  false.
Proof.
  split.
  - apply electronic_occupancy_certifies_nuclear_decay_refuse.
  - unfold inb_conservation_verdict_ok.
    rewrite electronic_occupancy_certifies_nuclear_decay_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — isotope nuclear boundary refuse                       *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false true false =
  inb_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false true false =
  inb_verdict_proved_without_bar_refuse /\
  inb_conservation_verdict_ok
    (evaluate_inb_bundle
       isotope_nuclear_boundary_conservation_unwired
       inbPm61Witness
       inbClaimBarAbsent false false true false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold inb_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — isotope lattice not wired                   *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_proved false true =
  inb_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_proved false true) =
  false.
Proof.
  unfold inb_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel isotope axiom refuse — morphism not 26th axiom               *)
(* ------------------------------------------------------------------ *)

Definition isotopeNuclearBoundaryConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/isotope.rs".

Definition parallelInbAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_inb_axiom_refuse :
  isotopeNuclearBoundaryConservationAuthority <>
  parallelInbAxiomTag /\
  isotopeNuclearBoundaryConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply isotope_nuclear_boundary_conservation_proved_false.
Qed.

Theorem parallel_inb_axiom_not_minted :
  isotopeNuclearBoundaryConservationAuthority =
  "umst/umst-chem/src/l0_tables/isotope.rs" /\
  isotopeNuclearBoundaryConservationProved = false /\
  isotopeNuclearBoundaryConservationAuthority <> parallelInbAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — isotope ≠ L1 SpeciesId occupancy tag       *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition isotopeNuclearBoundaryConservationFraming : string :=
  "second_law_conservation_isotope_one_axiom".

Lemma species_id_smuggle_refuse :
  isotopeNuclearBoundaryConservationFraming <>
  speciesIdSmuggleFraming /\
  promethium_atomic_number_z = 61 /\
  pattern_class_inb_idx = 11.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem inb_not_species_id_smuggle :
  isotopeNuclearBoundaryConservationFraming <>
  speciesIdSmuggleFraming /\
  promethium_atomic_number_z = 61 /\
  pattern_class_inb_idx = 11 /\
  isotopeNuclearBoundaryConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — isotope ≠ Z=119 smuggle                      *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  isotopeNuclearBoundaryConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem inb_not_extra_element_id :
  isotopeNuclearBoundaryConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  promethium_atomic_number_z = 61.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins          *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_isotope_scaffold".

Lemma tp_float_pin_refuse :
  isotopeNuclearBoundaryConservationFraming <>
  tpFloatPinFraming /\
  nuclear_decay_channel_tag = "nuclear_decay_boundary".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  isotopeNuclearBoundaryConservationFraming <>
  tpFloatPinFraming /\
  electronic_chem_channel_tag = "electronic_occupancy" /\
  promethium_atomic_number_z = 61.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Isotope **conservation** coherence scaffold                           *)
(* ------------------------------------------------------------------ *)

Definition inb_conservation_coherence_scaffold : bool :=
  inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_proved false false) &&
  negb (inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_unwired true false)) &&
  negb (inb_conservation_verdict_ok
    (evaluate_isotope_nuclear_boundary_conservation_close
       isotope_nuclear_boundary_conservation_proved false true)).

Lemma inb_conservation_coherence_scaffold_true :
  inb_conservation_coherence_scaffold = true.
Proof.
  unfold inb_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem inb_conservation_coherence_scaffold_theorem :
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_proved false false =
    inb_verdict_named_ok /\
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_unwired true false =
    inb_verdict_green_invent_refuse /\
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_proved false true =
    inb_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting            *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition inb_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition inb_conservation_knowing_fiber_ok : bool :=
  inb_conservation_fiber_ok fiber_quantum_knowing.

Definition inb_conservation_meso_acting_ok : bool :=
  inb_conservation_fiber_ok fiber_meso_acting.

Lemma inb_conservation_knowing_fiber_ok_true :
  inb_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma inb_conservation_meso_acting_not_ok :
  inb_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem inb_conservation_routes_knowing_not_meso :
  inb_conservation_knowing_fiber_ok = true /\
  inb_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply inb_conservation_knowing_fiber_ok_true.
  - apply inb_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  inb_conservation_knowing_fiber_ok &&
  negb inb_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, inb_conservation_knowing_fiber_ok,
    inb_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-11 + fail-closed + fiber               *)
(* ------------------------------------------------------------------ *)

Theorem isotope_nuclear_boundary_conservation_fixture_scaffold :
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false false =
    inb_verdict_named_ok /\
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbEmptyWitness
    inbClaimBarAbsent false false false false =
    inb_verdict_trivial_refuse /\
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent true false false false =
    inb_verdict_xor_refuse /\
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false true false =
    inb_verdict_proved_without_bar_refuse /\
  evaluate_inb_bundle
    isotope_nuclear_boundary_conservation_unwired
    inbPm61Witness
    inbClaimBarAbsent false false false true =
    inb_verdict_electronic_occupancy_certifies_nuclear_decay_refuse /\
  evaluate_isotope_nuclear_boundary_conservation_close
    isotope_nuclear_boundary_conservation_unwired false false =
    inb_verdict_unwired_ok /\
  inb_conservation_knowing_fiber_ok = true /\
  inb_conservation_meso_acting_ok = false /\
  isotopeNuclearBoundaryConservationProved = false /\
  inbProductNotXor = true /\
  promethium_atomic_number_z = 61.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — isotope nuclear boundary)             *)
(* ------------------------------------------------------------------ *)

Definition chemL0InbTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/isotope.rs".

Definition inbBoundaryAuthority : string :=
  "umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeInbCellId : string := "CHEM-L0-EDGE-ISOTOPE".

Definition chemIntNuanceInbCellId : string := "CHEM-INT-NUANCE-ISOTOPE".

Definition isotopeNuclearBoundaryConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION".

Definition isotopeNuclearBoundaryConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION IsotopeNuclearBoundaryConservationModality Unwired Assumed Proved Surrogate four-step lattice isotopeNuclearBoundaryConservationProved false evaluateIsotopeBundle evaluateIsotopeNuclearBoundaryConservation named class 11 isotope nuclear boundary Pm Z=61 electronic chemistry nuclear decay radioactivity concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel isotope axiom refuse species id smuggle refuse extra element id Z=119 refuse electronic occupancy certifies nuclear decay refuse isotope ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma isotope_nuclear_boundary_conservation_cell_id :
  isotopeNuclearBoundaryConservationCellId =
  "CHEM-FORMAL-Q-COQ-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION".
Proof. reflexivity. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_l0_table :
  chemL0InbTableAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_nuclear_boundary_conservation_authority_path :
  isotopeNuclearBoundaryConservationAuthority =
  "umst/umst-chem/src/l0_tables/isotope.rs".
Proof. reflexivity. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_boundary :
  inbBoundaryAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_marker :
  inbConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_edge_cell :
  chemL0EdgeInbCellId = "CHEM-L0-EDGE-ISOTOPE".
Proof. reflexivity. Qed.

Lemma isotope_nuclear_boundary_conservation_cites_nuance_cell :
  chemIntNuanceInbCellId = "CHEM-INT-NUANCE-ISOTOPE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom     *)
(* ------------------------------------------------------------------ *)

Lemma inb_not_26th_axiom :
  isotopeNuclearBoundaryConservationFraming <> parallelInbAxiomTag.
Proof. discriminate. Qed.

Lemma inb_second_law_conservation_framing :
  isotopeNuclearBoundaryConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma isotope_nuclear_boundary_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma isotope_nuclear_boundary_conservation_modality_unwired :
  isotopeNuclearBoundaryConservationModalityCurrent =
  isotope_nuclear_boundary_conservation_unwired.
Proof. reflexivity. Qed.

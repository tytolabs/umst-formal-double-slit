(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PerElementNuanceConservation.v                        *)
(*                                                                      *)
(*  Knowing-fiber Coq: PATTERN-00 class 0 **per_element_nuance**       *)
(*  **conservation**. Concurrent Π_c factor in PatternBundle product  *)
(*  (cardinality 25; class 0 present slot is **product**, not XOR).     *)
(*  Occupied Q-lattice cell; homolog ≠ copy (Ds vs Pt). XOR mutually-   *)
(*  exclusive classifiers refuse. Trivial empty-Z refuse fail-closed;   *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed. Geometry  *)
(*  routes knowing/quantum fiber not meso acting. Not 118² GREEN table. *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — per-element nuance is not a 26th axiom. *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 class 0 **per_element_nuance** **conservation** modality *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PerElementNuanceConservationModality : Type :=
  | per_element_nuance_conservation_unwired
  | per_element_nuance_conservation_assumed
  | per_element_nuance_conservation_proved
  | per_element_nuance_conservation_surrogate.

Definition perElementNuanceConservationModalityCurrent : PerElementNuanceConservationModality :=
  per_element_nuance_conservation_unwired.

Definition per_element_nuance_modality_lattice_cardinality : nat := 4.

Lemma per_element_nuance_modality_lattice_cardinality_is_four :
  per_element_nuance_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma per_element_nuance_modality_lattice_not_118_squared :
  negb (Nat.eqb per_element_nuance_modality_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold per_element_nuance_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern class 0 — per_element_nuance concurrent Π_c factor (not XOR) *)
(* ------------------------------------------------------------------ *)

Definition pattern_class_per_element_nuance_idx : nat := 0.

Lemma pattern_class_per_element_nuance_idx_is_0 :
  pattern_class_per_element_nuance_idx = 0.
Proof. reflexivity. Qed.

Definition pattern_class_cardinality : nat := 25.

Lemma pattern_class_cardinality_is_25 :
  pattern_class_cardinality = 25.
Proof. reflexivity. Qed.

Definition pattern_class_index_valid (i : nat) : bool :=
  Nat.ltb i pattern_class_cardinality.

Lemma per_element_nuance_class_index_valid :
  pattern_class_index_valid pattern_class_per_element_nuance_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_per_element_nuance_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Lemma pattern_class_not_118_squared :
  negb (Nat.eqb pattern_class_cardinality (118 * 118)) = true.
Proof.
  unfold pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierPerElementNuanceRowId : string := "X00".

Lemma cross_classifier_per_element_nuance_row_named :
  crossClassifierPerElementNuanceRowId = "X00".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — per-element nuance table [118] keyed by Z           *)
(*  (not 118² GREEN table)                                             *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition per_element_nuance_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition per_element_nuance_iron_z : nat := 26.
Definition per_element_nuance_copper_z : nat := 29.
Definition per_element_nuance_platinum_z : nat := 78.
Definition per_element_nuance_darmstadtium_z : nat := 110.

Lemma per_element_nuance_iron_z_is_26 :
  per_element_nuance_iron_z = 26.
Proof. reflexivity. Qed.

Lemma per_element_nuance_copper_z_is_29 :
  per_element_nuance_copper_z = 29.
Proof. reflexivity. Qed.

Lemma per_element_nuance_platinum_z_is_78 :
  per_element_nuance_platinum_z = 78.
Proof. reflexivity. Qed.

Lemma per_element_nuance_darmstadtium_z_is_110 :
  per_element_nuance_darmstadtium_z = 110.
Proof. reflexivity. Qed.

Lemma per_element_nuance_fe_cu_z_valid :
  per_element_nuance_z_valid per_element_nuance_iron_z = true /\
  per_element_nuance_z_valid per_element_nuance_copper_z = true.
Proof.
  repeat split;
  unfold per_element_nuance_z_valid, iupac_table_cardinality; reflexivity.
Qed.

Lemma per_element_nuance_pt_ds_z_valid :
  per_element_nuance_z_valid per_element_nuance_platinum_z = true /\
  per_element_nuance_z_valid per_element_nuance_darmstadtium_z = true.
Proof.
  repeat split;
  unfold per_element_nuance_z_valid, iupac_table_cardinality; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Occupied Q-lattice cell — PRIMARY discrete identity per Z           *)
(* ------------------------------------------------------------------ *)

Inductive qlattice_cell_posture : Type :=
  | qlattice_cell_unwired
  | qlattice_cell_occupied
  | qlattice_cell_absent.

Definition qlattice_cell_is_occupied (c : qlattice_cell_posture) : bool :=
  match c with
  | qlattice_cell_occupied => true
  | _ => false
  end.

Definition qlattice_cell_is_unwired (c : qlattice_cell_posture) : bool :=
  match c with
  | qlattice_cell_unwired => true
  | _ => false
  end.

Record per_element_qlattice_binding : Type := {
  qlattice_parent_z : nat;
  qlattice_cell : qlattice_cell_posture
}.

Definition perElementQlatticeIronOccupied : per_element_qlattice_binding :=
  {| qlattice_parent_z := per_element_nuance_iron_z;
     qlattice_cell := qlattice_cell_occupied |}.

Definition perElementQlatticeCopperOccupied : per_element_qlattice_binding :=
  {| qlattice_parent_z := per_element_nuance_copper_z;
     qlattice_cell := qlattice_cell_occupied |}.

Definition perElementQlatticeTrivial : per_element_qlattice_binding :=
  {| qlattice_parent_z := 0;
     qlattice_cell := qlattice_cell_unwired |}.

Definition perElementQlatticeBindingNontrivial (b : per_element_qlattice_binding) : bool :=
  Nat.ltb 0 (qlattice_parent_z b) &&
  qlattice_cell_is_occupied (qlattice_cell b).

Lemma iron_qlattice_occupied_nontrivial :
  perElementQlatticeBindingNontrivial perElementQlatticeIronOccupied = true.
Proof. reflexivity. Qed.

Lemma copper_qlattice_occupied_nontrivial :
  perElementQlatticeBindingNontrivial perElementQlatticeCopperOccupied = true.
Proof. reflexivity. Qed.

Lemma trivial_qlattice_not_nontrivial :
  perElementQlatticeBindingNontrivial perElementQlatticeTrivial = false.
Proof. reflexivity. Qed.

Definition qlatticeBindingIdentityConserved (b1 b2 : per_element_qlattice_binding) : bool :=
  Nat.eqb (qlattice_parent_z b1) (qlattice_parent_z b2).

Lemma iron_copper_distinct_z :
  negb (Nat.eqb per_element_nuance_iron_z per_element_nuance_copper_z) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog ≠ copy — Ds (Z=110) is not a Pt (Z=78) identity copy       *)
(* ------------------------------------------------------------------ *)

Definition periodHomologZOffset : nat := 32.

Lemma period_homolog_z_offset_is_32 : periodHomologZOffset = 32%nat.
Proof. reflexivity. Qed.

Lemma ds_pt_homolog_z_offset :
  per_element_nuance_darmstadtium_z = per_element_nuance_platinum_z + periodHomologZOffset.
Proof.
  unfold per_element_nuance_darmstadtium_z, per_element_nuance_platinum_z,
    periodHomologZOffset.
  reflexivity.
Qed.

Definition homologNotCopyWitness : bool :=
  negb (Nat.eqb per_element_nuance_darmstadtium_z per_element_nuance_platinum_z).

Lemma homolog_not_copy_witness_true : homologNotCopyWitness = true.
Proof. reflexivity. Qed.

Definition homologCopyTheaterMarker : string :=
  "homolog Ds Z=110 ne Pt Z=78 occupancy copy theater".

Lemma homolog_copy_theater_named :
  homologCopyTheaterMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Per-element nuance slot — concurrent **product** factor, not XOR     *)
(* ------------------------------------------------------------------ *)

Inductive per_element_nuance_slot : Type :=
  | nuance_slot_unwired
  | nuance_slot_absent
  | nuance_slot_present.

Definition per_element_nuance_slot_beq (s1 s2 : per_element_nuance_slot) : bool :=
  match s1, s2 with
  | nuance_slot_unwired, nuance_slot_unwired => true
  | nuance_slot_absent, nuance_slot_absent => true
  | nuance_slot_present, nuance_slot_present => true
  | _, _ => false
  end.

Definition per_element_nuance_slot_is_present (s : per_element_nuance_slot) : bool :=
  match s with
  | nuance_slot_present => true
  | _ => false
  end.

Definition perElementNuanceUnwiredSlot : per_element_nuance_slot := nuance_slot_unwired.
Definition perElementNuanceAbsentSlot : per_element_nuance_slot := nuance_slot_absent.
Definition perElementNuancePresentSlot : per_element_nuance_slot := nuance_slot_present.

Lemma present_nuance_slot_is_present :
  per_element_nuance_slot_is_present nuance_slot_present = true.
Proof. reflexivity. Qed.

Lemma unwired_nuance_slot_not_present :
  per_element_nuance_slot_is_present nuance_slot_unwired = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PatternBundle_25 — Π_c concurrent **product** scaffold              *)
(*  Class 0 per_element_nuance + concurrent factors at other indices    *)
(* ------------------------------------------------------------------ *)

Definition pattern_bundle : Type := nat -> per_element_nuance_slot.

Definition patternBundleAllUnwired : pattern_bundle :=
  fun _ => nuance_slot_unwired.

Definition patternBundleAt (b : pattern_bundle) (idx : nat)
  (slot : per_element_nuance_slot) : pattern_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition patternBundleWithPresent (b : pattern_bundle) (idx : nat) : pattern_bundle :=
  patternBundleAt b idx nuance_slot_present.

Fixpoint count_present_up_to (b : pattern_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if per_element_nuance_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_present_up_to b i + add
  end.

Definition patternBundlePresentCount (b : pattern_bundle) : nat :=
  count_present_up_to b pattern_class_cardinality.

Definition patternBundleHolds (b : pattern_bundle) (idx : nat) : bool :=
  per_element_nuance_slot_is_present (b idx).

Definition patternBundleIsConcurrentProduct (b : pattern_bundle) : bool :=
  Nat.leb 2 (patternBundlePresentCount b).

Fixpoint pattern_bundle_slots_match_up_to
  (b1 b2 : pattern_bundle) (bound : nat) : bool :=
  match bound with
  | 0 => true
  | S i =>
      per_element_nuance_slot_beq (b1 (pred bound)) (b2 (pred bound)) &&
      pattern_bundle_slots_match_up_to b1 b2 i
  end.

Definition patternBundleIdentityConserved (b1 b2 : pattern_bundle) : bool :=
  pattern_bundle_slots_match_up_to b1 b2 pattern_class_cardinality.

Definition pattern_class_allotrope_idx : nat := 10.
Definition pattern_class_catalysis_idx : nat := 14.
Definition pattern_class_continuum_idx : nat := 23.

(* Class 0 per_element_nuance + allotrope + catalysis concurrent witness. *)
Definition patternBundlePerElementNuanceWitness : pattern_bundle :=
  patternBundleWithPresent
    (patternBundleWithPresent
      (patternBundleWithPresent patternBundleAllUnwired
        pattern_class_per_element_nuance_idx)
      pattern_class_allotrope_idx)
    pattern_class_catalysis_idx.

Definition patternBundleEmptyWitness : pattern_bundle :=
  patternBundleAllUnwired.

Definition patternBundleSinglePresent : pattern_bundle :=
  patternBundleWithPresent patternBundleAllUnwired pattern_class_per_element_nuance_idx.

Lemma per_element_nuance_class0_present :
  patternBundleHolds patternBundlePerElementNuanceWitness
    pattern_class_per_element_nuance_idx = true.
Proof. reflexivity. Qed.

Lemma per_element_nuance_allotrope_present :
  patternBundleHolds patternBundlePerElementNuanceWitness
    pattern_class_allotrope_idx = true.
Proof. reflexivity. Qed.

Lemma per_element_nuance_catalysis_present :
  patternBundleHolds patternBundlePerElementNuanceWitness
    pattern_class_catalysis_idx = true.
Proof. reflexivity. Qed.

Lemma per_element_nuance_present_count_is_three :
  patternBundlePresentCount patternBundlePerElementNuanceWitness = 3.
Proof. reflexivity. Qed.

Lemma per_element_nuance_is_concurrent_product :
  patternBundleIsConcurrentProduct patternBundlePerElementNuanceWitness = true.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite per_element_nuance_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  patternBundlePresentCount patternBundleEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleEmptyWitness = false.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  patternBundlePresentCount patternBundleSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleSinglePresent = false.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

Lemma per_element_nuance_identity_conserved :
  patternBundleIdentityConserved patternBundlePerElementNuanceWitness
    patternBundlePerElementNuanceWitness = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive xor_classifier_bucket : Type :=
  | xor_bucket_exclusive
  | xor_bucket_concurrent_product.

Definition xorClassifierMarker : string := "chem_l0_pattern_xor_classifier_v1".
Definition concurrentProductMarker : string := "chem_int_per_element_nuance_product_v1".

Lemma xor_marker_ne_concurrent_product_marker :
  xorClassifierMarker <> concurrentProductMarker.
Proof. discriminate. Qed.

Definition xorClassifierIncompatible (claim_xor : bool) (b : pattern_bundle) : bool :=
  claim_xor && patternBundleIsConcurrentProduct b.

Lemma xor_refuse_on_per_element_nuance :
  xorClassifierIncompatible true patternBundlePerElementNuanceWitness = true.
Proof.
  unfold xorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma xor_ok_on_concurrent_product_claim :
  xorClassifierIncompatible false patternBundlePerElementNuanceWitness = false.
Proof. reflexivity. Qed.

Definition productNotXor : bool :=
  patternBundleIsConcurrentProduct patternBundlePerElementNuanceWitness &&
  xorClassifierIncompatible true patternBundlePerElementNuanceWitness.

Lemma product_not_xor_true : productNotXor = true.
Proof.
  unfold productNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  productNotXor = true /\
  Nat.leb 2 (patternBundlePresentCount patternBundlePerElementNuanceWitness) = true /\
  xorClassifierMarker <> concurrentProductMarker.
Proof.
  split.
  - apply product_not_xor_true.
  - split.
    + rewrite per_element_nuance_present_count_is_three.
      reflexivity.
    + apply xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Per-element nuance bar — Proved-without-bar fail-closed             *)
(* ------------------------------------------------------------------ *)

Inductive per_element_nuance_bar_presence : Type :=
  | per_element_nuance_bar_absent
  | per_element_nuance_bar_present.

Record per_element_nuance_claim_bar : Type := {
  per_element_nuance_bar_presence_tag : per_element_nuance_bar_presence;
  per_element_nuance_bar_defect_total : nat
}.

Definition perElementNuanceClaimBarAbsent : per_element_nuance_claim_bar :=
  {| per_element_nuance_bar_presence_tag := per_element_nuance_bar_absent;
     per_element_nuance_bar_defect_total := 0 |}.

Definition perElementNuanceClaimBarZeroDefect : per_element_nuance_claim_bar :=
  {| per_element_nuance_bar_presence_tag := per_element_nuance_bar_present;
     per_element_nuance_bar_defect_total := 0 |}.

Definition per_element_nuance_claim_bar_zero_defect (b : per_element_nuance_claim_bar) : bool :=
  match per_element_nuance_bar_presence_tag b with
  | per_element_nuance_bar_absent => false
  | per_element_nuance_bar_present =>
      Nat.eqb (per_element_nuance_bar_defect_total b) 0
  end.

Lemma per_element_nuance_claim_bar_zero_defect_true :
  per_element_nuance_claim_bar_zero_defect perElementNuanceClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma per_element_nuance_claim_bar_absent_not_zero_defect :
  per_element_nuance_claim_bar_zero_defect perElementNuanceClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Per-element nuance **conservation** verdict — fail-closed lattice    *)
(* ------------------------------------------------------------------ *)

Inductive per_element_nuance_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_nuance_named_ok
  | verdict_trivial_z_refuse
  | verdict_xor_classifier_refuse
  | verdict_homolog_copy_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse
  | verdict_twenty_sixth_axiom_refuse.

Definition per_element_nuance_conservation_verdict_ok
  (v : per_element_nuance_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_nuance_named_ok => true
  | _ => false
  end.

Record per_element_nuance_incidence : Type := {
  nuance_inc_qlattice : per_element_qlattice_binding;
  nuance_inc_bundle : pattern_bundle;
  nuance_inc_level : nat
}.

Definition perElementNuanceIncidenceNontrivial (h : per_element_nuance_incidence) : bool :=
  Nat.ltb 0 (nuance_inc_level h) &&
  perElementQlatticeBindingNontrivial (nuance_inc_qlattice h).

Definition perElementNuanceIncidenceIronL1 : per_element_nuance_incidence :=
  {| nuance_inc_qlattice := perElementQlatticeIronOccupied;
     nuance_inc_bundle := patternBundlePerElementNuanceWitness;
     nuance_inc_level := 1 |}.

Definition perElementNuanceIncidenceCopperL1 : per_element_nuance_incidence :=
  {| nuance_inc_qlattice := perElementQlatticeCopperOccupied;
     nuance_inc_bundle := patternBundlePerElementNuanceWitness;
     nuance_inc_level := 1 |}.

Definition perElementNuanceIncidenceTrivial : per_element_nuance_incidence :=
  {| nuance_inc_qlattice := perElementQlatticeTrivial;
     nuance_inc_bundle := patternBundleEmptyWitness;
     nuance_inc_level := 0 |}.

Definition perElementNuanceIncidenceHomologCopy : per_element_nuance_incidence :=
  {| nuance_inc_qlattice :=
       {| qlattice_parent_z := per_element_nuance_darmstadtium_z;
          qlattice_cell := qlattice_cell_occupied |};
     nuance_inc_bundle := patternBundlePerElementNuanceWitness;
     nuance_inc_level := 1 |}.

Definition evaluate_per_element_nuance_incidence
  (m : PerElementNuanceConservationModality)
  (h : per_element_nuance_incidence)
  (bar : per_element_nuance_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_homolog_copy : bool)
  (claim_twenty_sixth_axiom : bool) : per_element_nuance_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_twenty_sixth_axiom
            then verdict_twenty_sixth_axiom_refuse
            else if negb (perElementNuanceIncidenceNontrivial h)
                 then verdict_trivial_z_refuse
                 else if claim_homolog_copy
                      then verdict_homolog_copy_refuse
                      else if xorClassifierIncompatible claim_xor_classifier
                               (nuance_inc_bundle h)
                           then verdict_xor_classifier_refuse
                           else
                             match m with
                             | per_element_nuance_conservation_unwired =>
                                 verdict_nuance_named_ok
                             | per_element_nuance_conservation_assumed
                             | per_element_nuance_conservation_surrogate =>
                                 verdict_unwired_ok
                             | per_element_nuance_conservation_proved =>
                                 verdict_proved_without_bar_refuse
                             end.

Definition evaluate_per_element_nuance_conservation_close
  (m : PerElementNuanceConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : per_element_nuance_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | per_element_nuance_conservation_unwired => verdict_unwired_ok
    | per_element_nuance_conservation_assumed
    | per_element_nuance_conservation_proved
    | per_element_nuance_conservation_surrogate => verdict_nuance_named_ok
    end.

Definition per_element_nuance_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_per_element_nuance_conservation_close
          per_element_nuance_conservation_proved claim_physics_green claim_production_wired with
  | verdict_nuance_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Per-element nuance law cells — Unwired                               *)
(* ------------------------------------------------------------------ *)

Inductive per_element_nuance_conservation_law : Type :=
  | law_per_element_nuance_named
  | law_xor_classifier_refuse
  | law_homolog_copy_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition per_element_nuance_conservation_law_count : nat := 5.

Lemma per_element_nuance_conservation_law_count_is_five :
  per_element_nuance_conservation_law_count = 5.
Proof. reflexivity. Qed.

Inductive per_element_nuance_conservation_law_witness : Type :=
  | per_element_nuance_law_witness_open
  | per_element_nuance_law_witness_proved.

Definition evaluate_per_element_nuance_conservation_law_witness
  (law : per_element_nuance_conservation_law) (m : PerElementNuanceConservationModality)
  : per_element_nuance_conservation_law_witness :=
  match m with
  | per_element_nuance_conservation_unwired
  | per_element_nuance_conservation_assumed
  | per_element_nuance_conservation_surrogate => per_element_nuance_law_witness_open
  | per_element_nuance_conservation_proved => per_element_nuance_law_witness_proved
  end.

Lemma all_per_element_nuance_conservation_laws_open_at_unwired :
  evaluate_per_element_nuance_conservation_law_witness law_per_element_nuance_named
    per_element_nuance_conservation_unwired = per_element_nuance_law_witness_open /\
  evaluate_per_element_nuance_conservation_law_witness law_xor_classifier_refuse
    per_element_nuance_conservation_unwired = per_element_nuance_law_witness_open /\
  evaluate_per_element_nuance_conservation_law_witness law_homolog_copy_refuse
    per_element_nuance_conservation_unwired = per_element_nuance_law_witness_open /\
  evaluate_per_element_nuance_conservation_law_witness law_green_invent_refuse
    per_element_nuance_conservation_unwired = per_element_nuance_law_witness_open /\
  evaluate_per_element_nuance_conservation_law_witness law_production_wired_refuse
    per_element_nuance_conservation_unwired = per_element_nuance_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 pins — perElementNuanceProved false                       *)
(* ------------------------------------------------------------------ *)

Definition perElementNuanceProved : bool := false.

Lemma per_element_nuance_proved_false : perElementNuanceProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

Definition twentySixthAxiomCollisionMarker : string :=
  "Per-element nuance class-0 Pi_c product ne 26th parallel chemistry axiom".

Lemma twenty_sixth_axiom_collision_named :
  twentySixthAxiomCollisionMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_unwired false false) =
  true.
Proof.
  unfold per_element_nuance_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named per-element nuance close — concurrent **product** **conservation** *)
(* ------------------------------------------------------------------ *)

Lemma per_element_nuance_named_ok :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false false false false =
  verdict_nuance_named_ok.
Proof. reflexivity. Qed.

Theorem named_per_element_nuance_conservation :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false false false false =
  verdict_nuance_named_ok /\
  patternBundleIdentityConserved patternBundlePerElementNuanceWitness
    patternBundlePerElementNuanceWitness = true /\
  patternBundleIsConcurrentProduct patternBundlePerElementNuanceWitness = true /\
  patternBundleHolds patternBundlePerElementNuanceWitness
    pattern_class_per_element_nuance_idx = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma per_element_nuance_named_close_ok :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_proved false false =
  verdict_nuance_named_ok.
Proof. reflexivity. Qed.

Theorem named_per_element_nuance_conservation_close :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_proved false false =
  verdict_nuance_named_ok /\
  per_element_nuance_conservation_authorized false false = true.
Proof.
  split.
  - apply per_element_nuance_named_close_ok.
  - unfold per_element_nuance_conservation_authorized.
    rewrite per_element_nuance_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial Z=0 fail-closed — per-element nuance refuse                *)
(* ------------------------------------------------------------------ *)

Lemma trivial_z_refused :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceTrivial
    perElementNuanceClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_z_fail_closed :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceTrivial
    perElementNuanceClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse /\
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_incidence
       per_element_nuance_conservation_unwired perElementNuanceIncidenceTrivial
       perElementNuanceClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold per_element_nuance_conservation_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse              *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent true false false false false =
  verdict_xor_classifier_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent true false false false false =
  verdict_xor_classifier_refuse /\
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_incidence
       per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
       perElementNuanceClaimBarAbsent true false false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold per_element_nuance_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog copy fail-closed — Ds ≠ Pt copy theater                     *)
(* ------------------------------------------------------------------ *)

Lemma homolog_copy_refused :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceHomologCopy
    perElementNuanceClaimBarAbsent false false false true false =
  verdict_homolog_copy_refuse.
Proof. reflexivity. Qed.

Theorem homolog_copy_fail_closed :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceHomologCopy
    perElementNuanceClaimBarAbsent false false false true false =
  verdict_homolog_copy_refuse /\
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_incidence
       per_element_nuance_conservation_unwired perElementNuanceIncidenceHomologCopy
       perElementNuanceClaimBarAbsent false false false true false) =
  false.
Proof.
  split.
  - apply homolog_copy_refused.
  - unfold per_element_nuance_conservation_verdict_ok.
    rewrite homolog_copy_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_unwired true false) =
  false.
Proof.
  unfold per_element_nuance_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_incidence_refuse :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false true false false false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — per-element nuance refuse          *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false true false false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false true false false =
  verdict_proved_without_bar_refuse /\
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_incidence
       per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
       perElementNuanceClaimBarAbsent false false true false false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold per_element_nuance_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — pattern lattice not production wired      *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_proved false true) =
  false.
Proof.
  unfold per_element_nuance_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  26th axiom refuse — not parallel per_element_nuance axiom           *)
(* ------------------------------------------------------------------ *)

Lemma twenty_sixth_axiom_refused :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false false false true =
  verdict_twenty_sixth_axiom_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Per-element nuance **conservation** coherence scaffold              *)
(* ------------------------------------------------------------------ *)

Definition per_element_nuance_conservation_coherence_scaffold : bool :=
  per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_proved false false) &&
  negb (per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_unwired true false)) &&
  negb (per_element_nuance_conservation_verdict_ok
    (evaluate_per_element_nuance_conservation_close
       per_element_nuance_conservation_proved false true)).

Lemma per_element_nuance_conservation_coherence_scaffold_true :
  per_element_nuance_conservation_coherence_scaffold = true.
Proof.
  unfold per_element_nuance_conservation_coherence_scaffold,
    per_element_nuance_conservation_verdict_ok.
  simpl.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_per_element_nuance_conservation.

Definition per_element_nuance_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition per_element_nuance_conservation_knowing_fiber_ok : bool :=
  per_element_nuance_conservation_fiber_ok fiber_quantum_knowing.

Definition per_element_nuance_conservation_meso_acting_ok : bool :=
  per_element_nuance_conservation_fiber_ok fiber_meso_acting.

Lemma per_element_nuance_knowing_fiber_ok_true :
  per_element_nuance_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma per_element_nuance_meso_acting_not_ok :
  per_element_nuance_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem per_element_nuance_routes_knowing_not_meso :
  per_element_nuance_conservation_knowing_fiber_ok = true /\
  per_element_nuance_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply per_element_nuance_knowing_fiber_ok_true.
  - apply per_element_nuance_meso_acting_not_ok.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named nuance + fail-closed + fiber + class 0   *)
(* ------------------------------------------------------------------ *)

Theorem per_element_nuance_conservation_fixture_scaffold :
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false false false false =
    verdict_nuance_named_ok /\
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceTrivial
    perElementNuanceClaimBarAbsent false false false false false =
    verdict_trivial_z_refuse /\
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent true false false false false =
    verdict_xor_classifier_refuse /\
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceIronL1
    perElementNuanceClaimBarAbsent false false true false false =
    verdict_proved_without_bar_refuse /\
  evaluate_per_element_nuance_incidence
    per_element_nuance_conservation_unwired perElementNuanceIncidenceHomologCopy
    perElementNuanceClaimBarAbsent false false false true false =
    verdict_homolog_copy_refuse /\
  evaluate_per_element_nuance_conservation_close
    per_element_nuance_conservation_unwired false false =
    verdict_unwired_ok /\
  per_element_nuance_conservation_knowing_fiber_ok = true /\
  per_element_nuance_conservation_meso_acting_ok = false /\
  perElementNuanceProved = false /\
  productNotXor = true /\
  homologNotCopyWitness = true /\
  pattern_class_per_element_nuance_idx = 0.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — read-only cites)     *)
(* ------------------------------------------------------------------ *)

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition perElementNuanceConservationIntAuthority : string :=
  "umst/umst-chem/src/x_rows/per_element_nuance_conservation.rs".

Definition chemIntCrossPerElementNuanceAuthority : string :=
  "CHEM-INT-CROSS-PER-ELEMENT-NUANCE-CONSERVATION".

Definition chemIntNuancePerElementNuanceAuthority : string :=
  "CHEM-INT-NUANCE-PER_ELEMENT_NUANCE".

Definition perElementNuanceConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PER-ELEMENT-NUANCE-CONSERVATION".

Definition perElementNuanceConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PER-ELEMENT-NUANCE-CONSERVATION PATTERN-00 class 0 per_element_nuance conservation concurrent Pi_c factor not XOR occupied Q-lattice homolog ne copy Ds Z=110 ne Pt Z=78 [118] keyed by Z trivial Z=0 refuse xor mutually exclusive classifiers refuse GREEN invent fail-closed proved-without-bar fail-closed perElementNuanceProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not 26th axiom not GREEN DFT not physics GREEN not production_wired".

Lemma per_element_nuance_conservation_cell_id :
  perElementNuanceConservationCellId =
  "CHEM-FORMAL-Q-COQ-PER-ELEMENT-NUANCE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma per_element_nuance_conservation_cites_pattern_product_conservation :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma per_element_nuance_conservation_cites_int_x_row :
  perElementNuanceConservationIntAuthority <> "".
Proof. discriminate. Qed.

Lemma per_element_nuance_conservation_cites_int_cross :
  chemIntCrossPerElementNuanceAuthority =
  "CHEM-INT-CROSS-PER-ELEMENT-NUANCE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma per_element_nuance_conservation_cites_int_nuance_table :
  chemIntNuancePerElementNuanceAuthority = "CHEM-INT-NUANCE-PER_ELEMENT_NUANCE".
Proof. reflexivity. Qed.

Lemma per_element_nuance_conservation_cites_x00_row :
  crossClassifierPerElementNuanceRowId = "X00".
Proof. reflexivity. Qed.

Lemma per_element_nuance_conservation_cites_marker :
  concurrentProductMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Definition perElementNuanceSecondLawConservationFraming : string :=
  "second_law_conservation_per_element_nuance_one_axiom_not_26th_axiom_not_homolog_copy".

Lemma per_element_nuance_not_26th_axiom :
  perElementNuanceSecondLawConservationFraming <> "26th_parallel_chemistry_axiom".
Proof. discriminate. Qed.

Lemma per_element_nuance_second_law_conservation_framing :
  perElementNuanceSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma per_element_nuance_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma per_element_nuance_conservation_modality_unwired :
  perElementNuanceConservationModalityCurrent = per_element_nuance_conservation_unwired.
Proof. reflexivity. Qed.

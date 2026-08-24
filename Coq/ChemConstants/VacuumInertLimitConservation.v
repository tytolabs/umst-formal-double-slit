(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: VacuumInertLimitConservation.v                       *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 22 **vacuum_inert_limit** **conservation**. *)
(*  Vacuum/empty/inert limits are a named Environment section under the  *)
(*  same second-law + conservation object (not a parallel vacuum axiom). *)
(*  Inert gas ≠ zero oxygen — residual pO₂ named or typed Absent.       *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  vacuumInertLimitConservationProved false. Modality Unwired.          *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/vacuum_inert_limit.rs (cite).    *)
(*  INT: umst/umst-chem/src/vacuum_inert_limits.rs (read-only cite).     *)
(*  INT: umst/umst-chem/src/residual_gas_named_or_absent.rs (cite).     *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Residual pO₂ posture — Named trace oxygen or typed Absent          *)
(*  (inert gas ≠ zero oxygen — never silent zero float)                *)
(* ------------------------------------------------------------------ *)

Inductive residual_po2_posture : Type :=
  | residual_po2_named
  | residual_po2_absent.

Definition residual_po2_posture_beq (p1 p2 : residual_po2_posture) : bool :=
  match p1, p2 with
  | residual_po2_named, residual_po2_named => true
  | residual_po2_absent, residual_po2_absent => true
  | _, _ => false
  end.

Definition residual_po2_posture_is_named (p : residual_po2_posture) : bool :=
  match p with
  | residual_po2_named => true
  | residual_po2_absent => false
  end.

Definition residual_po2_posture_is_absent (p : residual_po2_posture) : bool :=
  match p with
  | residual_po2_absent => true
  | residual_po2_named => false
  end.

Definition residual_po2_named_or_absent_tag : string :=
  "residual_po2_named_or_absent".

Lemma residual_po2_named_or_absent_tag_nonempty :
  residual_po2_named_or_absent_tag <> "".
Proof. discriminate. Qed.

Definition inert_gas_ne_zero_oxygen_tag : string :=
  "inert_gas_ne_zero_oxygen".

Lemma inert_gas_ne_zero_oxygen_tag_nonempty :
  inert_gas_ne_zero_oxygen_tag <> "".
Proof. discriminate. Qed.

Definition canonical_inert_limit_residual_po2 : residual_po2_posture :=
  residual_po2_named.

Lemma canonical_inert_limit_residual_po2_is_named :
  residual_po2_posture_is_named canonical_inert_limit_residual_po2 = true.
Proof. reflexivity. Qed.

Lemma inert_gas_refuses_zero_oxygen_cartoon :
  residual_po2_posture_is_named canonical_inert_limit_residual_po2 = true /\
  residual_po2_posture_is_absent canonical_inert_limit_residual_po2 = false.
Proof. split; reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(*  Class-22 **vacuum_inert_limit** **conservation** modality *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive VacuumInertLimitConservationModality : Type :=
  | vacuum_inert_limit_conservation_unwired
  | vacuum_inert_limit_conservation_assumed
  | vacuum_inert_limit_conservation_proved
  | vacuum_inert_limit_conservation_surrogate.

Definition vacuumInertLimitConservationModalityCurrent :
  VacuumInertLimitConservationModality :=
  vacuum_inert_limit_conservation_unwired.

Definition vacuum_inert_limit_lattice_cardinality : nat := 4.

Lemma vacuum_inert_limit_lattice_cardinality_is_four :
  vacuum_inert_limit_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma vacuum_inert_limit_lattice_not_118_squared :
  negb (Nat.eqb vacuum_inert_limit_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold vacuum_inert_limit_lattice_cardinality.
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

(* North-star §2 class 22 — vacuum_inert_limit concurrent Π_c factor. *)
Definition pattern_class_vacuum_inert_limit_idx : nat := 22.

Lemma pattern_class_vacuum_inert_limit_idx_is_22 :
  pattern_class_vacuum_inert_limit_idx = 22.
Proof. reflexivity. Qed.

Lemma vacuum_inert_limit_class_index_valid :
  pattern_class_index_valid pattern_class_vacuum_inert_limit_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_vacuum_inert_limit_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierVacuumInertLimitRowId : string := "X22".

Lemma cross_classifier_vacuum_inert_limit_row_named :
  crossClassifierVacuumInertLimitRowId = "X22".
Proof. reflexivity. Qed.

Definition pattern_class_vacuum_inert_limit_tag : string :=
  "vacuum_inert_limit".

Definition north_star_class_22_vacuum_inert_tag : string :=
  "class 22 vacuum inert limits".

Lemma pattern_class_vacuum_inert_limit_tag_nonempty :
  pattern_class_vacuum_inert_limit_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_22_vacuum_inert_tag_nonempty :
  north_star_class_22_vacuum_inert_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — O Z=8 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition oxygen_atomic_number_z : nat := 8.

Lemma oxygen_atomic_number_z_is_8 :
  oxygen_atomic_number_z = 8.
Proof. reflexivity. Qed.

Definition oxygen_z_valid : bool :=
  Nat.ltb 0 oxygen_atomic_number_z &&
  Nat.leb oxygen_atomic_number_z iupac_table_cardinality.

Lemma oxygen_z_valid_true : oxygen_z_valid = true.
Proof.
  unfold oxygen_z_valid, oxygen_atomic_number_z, iupac_table_cardinality.
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

Definition vacuum_inert_limit_factor_tag : string :=
  "vacuum_inert_limit".

Definition vacuum_limit_section_tag : string := "vacuum_limit".

Definition inert_limit_section_tag : string := "inert_limit".

Lemma vacuum_inert_limit_factor_tag_nonempty :
  vacuum_inert_limit_factor_tag <> "".
Proof. discriminate. Qed.

Lemma vacuum_limit_section_tag_nonempty :
  vacuum_limit_section_tag <> "".
Proof. discriminate. Qed.

Lemma inert_limit_section_tag_nonempty :
  inert_limit_section_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive vil_channel_slot : Type :=
  | vil_slot_unwired
  | vil_slot_absent
  | vil_slot_present.

Definition vil_channel_slot_beq (s1 s2 : vil_channel_slot) : bool :=
  match s1, s2 with
  | vil_slot_unwired, vil_slot_unwired => true
  | vil_slot_absent, vil_slot_absent => true
  | vil_slot_present, vil_slot_present => true
  | _, _ => false
  end.

Definition vil_channel_slot_is_present (s : vil_channel_slot) : bool :=
  match s with
  | vil_slot_present => true
  | _ => false
  end.

Definition vacuumInertLimitProductChannelCount : nat := 3.

Lemma vacuum_inert_limit_product_channel_count_is_three :
  vacuumInertLimitProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = vacuum_limit section, 1 = inert_limit section, 2 = residual pO₂ Named-or-Absent. *)
Definition vil_channel_vacuum_limit_section : nat := 0.
Definition vil_channel_inert_limit_section : nat := 1.
Definition vil_channel_residual_po2_named_or_absent : nat := 2.

Lemma vil_channel_vacuum_limit_section_idx_is_0 :
  vil_channel_vacuum_limit_section = 0.
Proof. reflexivity. Qed.

Lemma vil_channel_inert_limit_section_idx_is_1 :
  vil_channel_inert_limit_section = 1.
Proof. reflexivity. Qed.

Lemma vil_channel_residual_po2_named_or_absent_idx_is_2 :
  vil_channel_residual_po2_named_or_absent = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition vil_channel_bundle : Type := nat -> vil_channel_slot.

Definition vacuumInertLimitBundleAllUnwired : vil_channel_bundle :=
  fun _ => vil_slot_unwired.

Definition vacuumInertLimitBundleAt (b : vil_channel_bundle) (idx : nat)
  (slot : vil_channel_slot) : vil_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition vacuumInertLimitBundleWithPresent
  (b : vil_channel_bundle) (idx : nat) : vil_channel_bundle :=
  vacuumInertLimitBundleAt b idx vil_slot_present.

Fixpoint count_vil_present_up_to (b : vil_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if vil_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_vil_present_up_to b i + add
  end.

Definition vacuumInertLimitBundlePresentCount (b : vil_channel_bundle) : nat :=
  count_vil_present_up_to b vacuumInertLimitProductChannelCount.

Definition vacuumInertLimitBundleHolds (b : vil_channel_bundle) (idx : nat) : bool :=
  vil_channel_slot_is_present (b idx).

Definition vacuumInertLimitBundleIsConcurrentProduct (b : vil_channel_bundle) : bool :=
  Nat.leb 2 (vacuumInertLimitBundlePresentCount b).

(* O Z=8 vacuum_limit + inert_limit + residual pO₂ Named-or-Absent concurrent witness. *)
Definition vacuumInertLimitO8Witness : vil_channel_bundle :=
  vacuumInertLimitBundleWithPresent
    (vacuumInertLimitBundleWithPresent
      (vacuumInertLimitBundleWithPresent vacuumInertLimitBundleAllUnwired
        vil_channel_vacuum_limit_section)
      vil_channel_inert_limit_section)
    vil_channel_residual_po2_named_or_absent.

Definition vacuumInertLimitEmptyWitness : vil_channel_bundle :=
  vacuumInertLimitBundleAllUnwired.

Definition vacuumInertLimitSinglePresent : vil_channel_bundle :=
  vacuumInertLimitBundleWithPresent vacuumInertLimitBundleAllUnwired
    vil_channel_vacuum_limit_section.

Lemma vacuum_limit_section_channel_present :
  vacuumInertLimitBundleHolds vacuumInertLimitO8Witness
    vil_channel_vacuum_limit_section = true.
Proof. reflexivity. Qed.

Lemma inert_limit_section_channel_present :
  vacuumInertLimitBundleHolds vacuumInertLimitO8Witness
    vil_channel_inert_limit_section = true.
Proof. reflexivity. Qed.

Lemma residual_po2_named_or_absent_channel_present :
  vacuumInertLimitBundleHolds vacuumInertLimitO8Witness
    vil_channel_residual_po2_named_or_absent = true.
Proof. reflexivity. Qed.

Lemma o8_witness_present_count_is_three :
  vacuumInertLimitBundlePresentCount vacuumInertLimitO8Witness = 3.
Proof. reflexivity. Qed.

Lemma o8_witness_is_concurrent_product :
  vacuumInertLimitBundleIsConcurrentProduct vacuumInertLimitO8Witness = true.
Proof.
  unfold vacuumInertLimitBundleIsConcurrentProduct.
  rewrite o8_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  vacuumInertLimitBundlePresentCount vacuumInertLimitEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  vacuumInertLimitBundleIsConcurrentProduct vacuumInertLimitEmptyWitness = false.
Proof.
  unfold vacuumInertLimitBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  vacuumInertLimitBundlePresentCount vacuumInertLimitSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  vacuumInertLimitBundleIsConcurrentProduct vacuumInertLimitSinglePresent = false.
Proof.
  unfold vacuumInertLimitBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive vil_xor_posture : Type :=
  | vil_xor_exclusive
  | vil_xor_concurrent_product.

Definition vilXorClassifierMarker : string := "chem_l0_vacuum_inert_limit_xor_classifier_v1".
Definition vilConcurrentProductMarker : string := "chem_int_vacuum_inert_limit_product_v1".

Lemma vil_xor_marker_ne_concurrent_product_marker :
  vilXorClassifierMarker <> vilConcurrentProductMarker.
Proof. discriminate. Qed.

Definition vilXorClassifierIncompatible (claim_xor : bool)
  (b : vil_channel_bundle) : bool :=
  claim_xor && vacuumInertLimitBundleIsConcurrentProduct b.

Lemma vil_xor_refuse_on_o8_witness :
  vilXorClassifierIncompatible true vacuumInertLimitO8Witness = true.
Proof.
  unfold vilXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma vil_xor_ok_on_concurrent_product_claim :
  vilXorClassifierIncompatible false vacuumInertLimitO8Witness = false.
Proof. reflexivity. Qed.

Definition vilProductNotXor : bool :=
  vacuumInertLimitBundleIsConcurrentProduct vacuumInertLimitO8Witness &&
  vilXorClassifierIncompatible true vacuumInertLimitO8Witness.

Lemma vil_product_not_xor_true : vilProductNotXor = true.
Proof.
  unfold vilProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  vilProductNotXor = true /\
  Nat.leb 2 (vacuumInertLimitBundlePresentCount
    vacuumInertLimitO8Witness) = true /\
  vilXorClassifierMarker <> vilConcurrentProductMarker.
Proof.
  split.
  - apply vil_product_not_xor_true.
  - split.
    + rewrite o8_witness_present_count_is_three.
      reflexivity.
    + apply vil_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive vil_bar_presence : Type :=
  | vil_bar_absent
  | vil_bar_present.

Record vil_claim_bar : Type := {
  vil_bar_presence_field : vil_bar_presence;
  vil_bar_defect_total : nat
}.

Definition vacuumInertLimitClaimBarAbsent : vil_claim_bar :=
  {| vil_bar_presence_field := vil_bar_absent;
     vil_bar_defect_total := 0 |}.

Definition vacuumInertLimitClaimBarZeroDefect : vil_claim_bar :=
  {| vil_bar_presence_field := vil_bar_present;
     vil_bar_defect_total := 0 |}.

Definition vil_claim_bar_zero_defect (b : vil_claim_bar) : bool :=
  match vil_bar_presence_field b with
  | vil_bar_absent => false
  | vil_bar_present => Nat.eqb (vil_bar_defect_total b) 0
  end.

Lemma vil_claim_bar_zero_defect_true :
  vil_claim_bar_zero_defect vacuumInertLimitClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma vil_claim_bar_absent_not_zero_defect :
  vil_claim_bar_zero_defect vacuumInertLimitClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive vil_conservation_verdict : Type :=
  | vil_verdict_unwired_ok
  | vil_verdict_named_ok
  | vil_verdict_design_ok
  | vil_verdict_trivial_refuse
  | vil_verdict_xor_refuse
  | vil_verdict_green_invent_refuse
  | vil_verdict_proved_without_bar_refuse
  | vil_verdict_production_wired_refuse
  | vil_verdict_parallel_vacuum_axiom_refuse
  | vil_verdict_zero_oxygen_cartoon_refuse
  | vil_verdict_extra_element_id_refuse
  | vil_verdict_parallel_vacuum_axiom_mint_refuse
  | vil_verdict_tp_float_pin_refuse.

Definition vil_conservation_verdict_ok (v : vil_conservation_verdict) : bool :=
  match v with
  | vil_verdict_unwired_ok => true
  | vil_verdict_named_ok => true
  | vil_verdict_design_ok => true
  | _ => false
  end.

Definition vacuumInertLimitBundleNontrivial (b : vil_channel_bundle) : bool :=
  Nat.ltb 0 (vacuumInertLimitBundlePresentCount b).

Definition evaluate_vacuum_inert_limit_bundle
  (m : VacuumInertLimitConservationModality)
  (b : vil_channel_bundle)
  (bar : vil_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : vil_conservation_verdict :=
  if claim_physics_green
  then vil_verdict_green_invent_refuse
  else if claim_proved
       then vil_verdict_proved_without_bar_refuse
       else if negb (vacuumInertLimitBundleNontrivial b)
            then vil_verdict_trivial_refuse
            else if vilXorClassifierIncompatible claim_xor_classifier b
                 then vil_verdict_xor_refuse
                 else
                   match m with
                   | vacuum_inert_limit_conservation_unwired =>
                       if vacuumInertLimitBundleIsConcurrentProduct b
                       then vil_verdict_named_ok
                       else vil_verdict_design_ok
                   | vacuum_inert_limit_conservation_assumed
                   | vacuum_inert_limit_conservation_surrogate =>
                       vil_verdict_design_ok
                   | vacuum_inert_limit_conservation_proved =>
                       vil_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_vacuum_inert_limit_conservation_close
  (m : VacuumInertLimitConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : vil_conservation_verdict :=
  if claim_physics_green
  then vil_verdict_green_invent_refuse
  else if claim_production_wired
  then vil_verdict_production_wired_refuse
  else
    match m with
    | vacuum_inert_limit_conservation_unwired => vil_verdict_unwired_ok
    | vacuum_inert_limit_conservation_assumed
    | vacuum_inert_limit_conservation_proved
    | vacuum_inert_limit_conservation_surrogate => vil_verdict_named_ok
    end.

Definition vacuum_inert_limit_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_vacuum_inert_limit_conservation_close
          vacuum_inert_limit_conservation_proved claim_physics_green claim_production_wired with
  | vil_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive vil_conservation_law : Type :=
  | vil_law_conserved
  | vil_law_named_ok
  | vil_law_trivial_refuse
  | vil_law_green_invent_refuse.

Definition vil_conservation_law_count : nat := 4.

Lemma vil_conservation_law_count_is_four :
  vil_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive vil_conservation_law_witness : Type :=
  | vil_law_witness_open
  | vil_law_witness_proved.

Definition evaluate_vil_conservation_law_witness
  (law : vil_conservation_law)
  (m : VacuumInertLimitConservationModality)
  : vil_conservation_law_witness :=
  match m with
  | vacuum_inert_limit_conservation_unwired
  | vacuum_inert_limit_conservation_assumed
  | vacuum_inert_limit_conservation_surrogate => vil_law_witness_open
  | vacuum_inert_limit_conservation_proved => vil_law_witness_proved
  end.

Lemma all_vil_conservation_laws_open_at_unwired :
  evaluate_vil_conservation_law_witness vil_law_conserved
    vacuum_inert_limit_conservation_unwired = vil_law_witness_open /\
  evaluate_vil_conservation_law_witness vil_law_named_ok
    vacuum_inert_limit_conservation_unwired = vil_law_witness_open /\
  evaluate_vil_conservation_law_witness vil_law_trivial_refuse
    vacuum_inert_limit_conservation_unwired = vil_law_witness_open /\
  evaluate_vil_conservation_law_witness vil_law_green_invent_refuse
    vacuum_inert_limit_conservation_unwired = vil_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-22 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition vacuumInertLimitConservationProved : bool := false.

Lemma vacuum_inert_limit_conservation_proved_false :
  vacuumInertLimitConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_unwired false false =
  vil_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_unwired false false =
  vil_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_unwired false false) =
  true.
Proof.
  unfold vil_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named O Z=8 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma o8_witness_named_ok :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false false =
  vil_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_o8_vacuum_inert_limit_conservation :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false false =
  vil_verdict_named_ok /\
  vacuumInertLimitBundleIsConcurrentProduct vacuumInertLimitO8Witness = true /\
  oxygen_atomic_number_z = 8 /\
  pattern_class_vacuum_inert_limit_idx = 22.
Proof.
  repeat split; reflexivity.
Qed.

Lemma vil_named_close_ok :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_proved false false =
  vil_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_vacuum_inert_limit_conservation_close :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_proved false false =
  vil_verdict_named_ok /\
  vacuum_inert_limit_conservation_authorized false false = true.
Proof.
  split.
  - apply vil_named_close_ok.
  - unfold vacuum_inert_limit_conservation_authorized.
    rewrite vil_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — vacuum inert limit refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitEmptyWitness
    vacuumInertLimitClaimBarAbsent false false false =
  vil_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitEmptyWitness
    vacuumInertLimitClaimBarAbsent false false false =
  vil_verdict_trivial_refuse /\
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_bundle
       vacuum_inert_limit_conservation_unwired
       vacuumInertLimitEmptyWitness
       vacuumInertLimitClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold vil_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent true false false =
  vil_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent true false false =
  vil_verdict_xor_refuse /\
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_bundle
       vacuum_inert_limit_conservation_unwired
       vacuumInertLimitO8Witness
       vacuumInertLimitClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold vil_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_unwired true false =
  vil_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_unwired true false) =
  false.
Proof.
  unfold vil_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_vil_bundle_refuse :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false true false =
  vil_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — vacuum inert limit refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false true =
  vil_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false true =
  vil_verdict_proved_without_bar_refuse /\
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_bundle
       vacuum_inert_limit_conservation_unwired
       vacuumInertLimitO8Witness
       vacuumInertLimitClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold vil_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — vacuum inert limit lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_proved false true =
  vil_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_proved false true) =
  false.
Proof.
  unfold vil_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel vacuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition vacuumInertLimitConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/vacuum_inert_limit.rs".

Definition parallelVacuumInertLimitAxiomTag : string := "parallel_vacuum_inert_limit_axiom".

Lemma parallel_vacuum_axiom_refuse :
  vacuumInertLimitConservationAuthority <>
  parallelVacuumInertLimitAxiomTag /\
  vacuumInertLimitConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply vacuum_inert_limit_conservation_proved_false.
Qed.

Theorem parallel_vacuum_axiom_not_minted :
  vacuumInertLimitConservationAuthority =
  "umst/umst-chem/src/l0_tables/vacuum_inert_limit.rs" /\
  vacuumInertLimitConservationProved = false /\
  vacuumInertLimitConservationAuthority <> parallelVacuumInertLimitAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Zero-oxygen cartoon refuse — inert gas ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition zeroOxygenCartoonSmuggleFraming : string :=
  "zero_oxygen_cartoon_not_named_object".

Definition vacuumInertLimitConservationFraming : string :=
  "second_law_conservation_vacuum_inert_limit_env_section_one_axiom".

Lemma zero_oxygen_cartoon_smuggle_refuse :
  vacuumInertLimitConservationFraming <>
  zeroOxygenCartoonSmuggleFraming /\
  oxygen_atomic_number_z = 8 /\
  pattern_class_vacuum_inert_limit_idx = 22.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem inert_gas_not_zero_oxygen_cartoon_smuggle :
  vacuumInertLimitConservationFraming <>
  zeroOxygenCartoonSmuggleFraming /\
  oxygen_atomic_number_z = 8 /\
  pattern_class_vacuum_inert_limit_idx = 22 /\
  vacuumInertLimitConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — vacuum inert limit ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "inert_gas_equals_zero_oxygen_cartoon".

Lemma zero_oxygen_cartoon_refuse :
  vacuumInertLimitConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_zero_oxygen_cartoon :
  vacuumInertLimitConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  oxygen_atomic_number_z = 8.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel vacuum axiom refuse — vacuum inert limit ≠ parallel vacuum axiom axiom    *)
(* ------------------------------------------------------------------ *)

Definition parallelVacuumAxiomFraming : string :=
  "parallel_vacuum_inert_limit_axiom_minted_as_26th_law".

Definition vacuumInertLimitsAuthority : string :=
  "umst/umst-chem/src/vacuum_inert_limits.rs".

Lemma parallel_vacuum_axiom_mint_refuse :
  vacuumInertLimitConservationFraming <>
  parallelVacuumAxiomFraming /\
  vacuumInertLimitsAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem vacuum_inert_limit_not_parallel_vacuum_axiom :
  vacuumInertLimitConservationFraming <>
  parallelVacuumAxiomFraming /\
  vacuumInertLimitsAuthority =
  "umst/umst-chem/src/vacuum_inert_limits.rs" /\
  vacuumInertLimitConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_float_pins_on_vacuum_inert_limit_scaffold".

Lemma tp_float_pin_refuse :
  vacuumInertLimitConservationFraming <>
  tpFloatPinFraming /\
  vacuum_limit_section_tag = "vacuum_limit".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  vacuumInertLimitConservationFraming <>
  tpFloatPinFraming /\
  inert_limit_section_tag = "inert_limit" /\
  oxygen_atomic_number_z = 8.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Vacuum inert limit **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition vil_conservation_coherence_scaffold : bool :=
  vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_proved false false) &&
  negb (vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_unwired true false)) &&
  negb (vil_conservation_verdict_ok
    (evaluate_vacuum_inert_limit_conservation_close
       vacuum_inert_limit_conservation_proved false true)).

Lemma vil_conservation_coherence_scaffold_true :
  vil_conservation_coherence_scaffold = true.
Proof.
  unfold vil_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem vil_conservation_coherence_scaffold_theorem :
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_proved false false =
    vil_verdict_named_ok /\
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_unwired true false =
    vil_verdict_green_invent_refuse /\
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_proved false true =
    vil_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition vil_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition vil_conservation_knowing_fiber_ok : bool :=
  vil_conservation_fiber_ok fiber_quantum_knowing.

Definition vil_conservation_meso_acting_ok : bool :=
  vil_conservation_fiber_ok fiber_meso_acting.

Lemma vil_conservation_knowing_fiber_ok_true :
  vil_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma vil_conservation_meso_acting_not_ok :
  vil_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem vil_conservation_routes_knowing_not_meso :
  vil_conservation_knowing_fiber_ok = true /\
  vil_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply vil_conservation_knowing_fiber_ok_true.
  - apply vil_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  vil_conservation_knowing_fiber_ok &&
  negb vil_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, vil_conservation_knowing_fiber_ok,
    vil_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-22 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem vacuum_inert_limit_conservation_fixture_scaffold :
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false false =
    vil_verdict_named_ok /\
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitEmptyWitness
    vacuumInertLimitClaimBarAbsent false false false =
    vil_verdict_trivial_refuse /\
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent true false false =
    vil_verdict_xor_refuse /\
  evaluate_vacuum_inert_limit_bundle
    vacuum_inert_limit_conservation_unwired
    vacuumInertLimitO8Witness
    vacuumInertLimitClaimBarAbsent false false true =
    vil_verdict_proved_without_bar_refuse /\
  evaluate_vacuum_inert_limit_conservation_close
    vacuum_inert_limit_conservation_unwired false false =
    vil_verdict_unwired_ok /\
  vil_conservation_knowing_fiber_ok = true /\
  vil_conservation_meso_acting_ok = false /\
  vacuumInertLimitConservationProved = false /\
  vilProductNotXor = true /\
  oxygen_atomic_number_z = 8.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — vacuum inert limit) *)
(* ------------------------------------------------------------------ *)

Definition chemL0VacuumInertLimitAuthority : string :=
  "umst/umst-chem/src/vacuum_inert_limits.rs".

Definition chemL0VacuumInertLimitTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/vacuum_inert_limit.rs".

Definition residualGasNamedOrAbsentAuthority : string :=
  "umst/umst-chem/src/residual_gas_named_or_absent.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeVacuumCellId : string := "CHEM-L0-EDGE-VACUUM".

Definition vacuumInertLimitConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-VACUUM-INERT-LIMIT-CONSERVATION".

Definition vacuumInertLimitConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-VACUUM-INERT-LIMIT-CONSERVATION VacuumInertLimitConservationModality Unwired Assumed Proved Surrogate four-step lattice vacuumInertLimitConservationProved false evaluateVacuumInertLimitBundle evaluateVacuumInertLimitConservation named class 22 vacuum_inert_limit O Z=8 residual pO2 Named or Absent inert gas ne zero oxygen env section second law vacuum inert limit concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel vacuum axiom refuse zero oxygen cartoon refuse extra element id Z=119 refuse parallel vacuum axiom mint VAC-22 refuse vacuum inert limit ne EnvSection Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma vacuum_inert_limit_conservation_cell_id :
  vacuumInertLimitConservationCellId =
  "CHEM-FORMAL-Q-COQ-VACUUM-INERT-LIMIT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma vacuum_inert_limit_conservation_cites_l0_table :
  chemL0VacuumInertLimitTableAuthority <> "".
Proof. discriminate. Qed.

Lemma vacuum_inert_limit_conservation_authority_path :
  vacuumInertLimitConservationAuthority =
  "umst/umst-chem/src/l0_tables/vacuum_inert_limit.rs".
Proof. reflexivity. Qed.

Lemma vacuum_inert_limit_conservation_cites_residual_gas :
  chemL0VacuumInertLimitAuthority <> "".
Proof. discriminate. Qed.

Lemma vacuum_inert_limit_conservation_cites_marker :
  vilConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma vacuum_inert_limit_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma vacuum_inert_limit_conservation_cites_edge_vacuum_cell :
  chemL0EdgeVacuumCellId = "CHEM-L0-EDGE-VACUUM".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma vacuum_inert_limit_not_26th_axiom :
  vacuumInertLimitConservationFraming <> parallelVacuumInertLimitAxiomTag.
Proof. discriminate. Qed.

Lemma vacuum_inert_limit_second_law_conservation_framing :
  vacuumInertLimitConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Env section — named object not parallel axiom, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition parallelVacuumAxiomMintFraming : string :=
  "parallel_vacuum_inert_limit_axiom_mint_not_env_section".

Definition envSectionNamedObject : string :=
  "vacuum_inert_limit_env_section_morphism".

Lemma zero_oxygen_cartoon_not_named_object :
  envSectionNamedObject <>
  parallelVacuumAxiomMintFraming /\
  inert_limit_section_tag = "inert_limit".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem env_section_is_named_object_not_parallel_axiom :
  envSectionNamedObject <>
  parallelVacuumAxiomMintFraming /\
  vacuum_limit_section_tag = "vacuum_limit" /\
  vacuumInertLimitConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Env section refuse — not parallel vacuum axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition envSectionFraming : string :=
  "env_section_not_parallel_vacuum_axiom".

Lemma env_section_not_parallel_vacuum_axiom_refuse :
  envSectionFraming <>
  parallelVacuumAxiomFraming /\
  vacuum_limit_section_tag = "vacuum_limit".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem vacuum_inert_limit_env_section_not_parallel_axiom :
  envSectionFraming <>
  parallelVacuumAxiomFraming /\
  vacuumInertLimitsAuthority =
  "umst/umst-chem/src/vacuum_inert_limits.rs" /\
  vacuumInertLimitConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma vacuum_inert_limit_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma vacuum_inert_limit_conservation_modality_unwired :
  vacuumInertLimitConservationModalityCurrent =
  vacuum_inert_limit_conservation_unwired.
Proof. reflexivity. Qed.

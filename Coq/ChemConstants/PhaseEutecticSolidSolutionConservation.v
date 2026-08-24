(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PhaseEutecticSolidSolutionConservation.v               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 13 **phase_eutectic_solid_solution**             *)
(*  **conservation**. Processing/refining is a concurrent PatternBundle factor on *)
(*  the same second-law + conservation object (not a 26th axiom). Concurrent Π_c   *)
(*  PatternBundle factor — **product** not XOR. phaseEutecticSolidSolutionConservationProved *)
(*  false. Modality Unwired.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/phase_eutectic_nonstoich.rs (read-only cite).       *)
(*  INT: umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs             *)
(*  (read-only cite). GRAPH cuts cited. PatternProductConservation.v   *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-13 **phase_eutectic_solid_solution** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PhaseEutecticSolidSolutionConservationModality : Type :=
  | phase_eutectic_solid_solution_conservation_unwired
  | phase_eutectic_solid_solution_conservation_assumed
  | phase_eutectic_solid_solution_conservation_proved
  | phase_eutectic_solid_solution_conservation_surrogate.

Definition phaseEutecticSolidSolutionConservationModalityCurrent :
  PhaseEutecticSolidSolutionConservationModality :=
  phase_eutectic_solid_solution_conservation_unwired.

Definition phase_eutectic_solid_solution_lattice_cardinality : nat := 4.

Lemma phase_eutectic_solid_solution_lattice_cardinality_is_four :
  phase_eutectic_solid_solution_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma phase_eutectic_solid_solution_lattice_not_118_squared :
  negb (Nat.eqb phase_eutectic_solid_solution_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold phase_eutectic_solid_solution_lattice_cardinality.
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

(* North-star §2 class 13 — phase_eutectic_solid_solution concurrent Π_c factor. *)
Definition pattern_class_phase_eutectic_solid_solution_idx : nat := 13.

Lemma pattern_class_phase_eutectic_solid_solution_idx_is_13 :
  pattern_class_phase_eutectic_solid_solution_idx = 13.
Proof. reflexivity. Qed.

Lemma phase_eutectic_solid_solution_class_index_valid :
  pattern_class_index_valid pattern_class_phase_eutectic_solid_solution_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_phase_eutectic_solid_solution_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierPhaseEutecticSolidSolutionRowId : string := "X13".

Lemma cross_classifier_phase_eutectic_solid_solution_row_named :
  crossClassifierPhaseEutecticSolidSolutionRowId = "X13".
Proof. reflexivity. Qed.

Definition pattern_class_phase_eutectic_solid_solution_tag : string :=
  "phase_eutectic_solid_solution".

Definition north_star_class_13_phase_eutectic_solid_solution_tag : string :=
  "class 13 phases".

Lemma pattern_class_phase_eutectic_solid_solution_tag_nonempty :
  pattern_class_phase_eutectic_solid_solution_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_13_phase_eutectic_solid_solution_tag_nonempty :
  north_star_class_13_phase_eutectic_solid_solution_tag <> "".
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

Definition phase_eutectic_solid_solution_factor_tag : string :=
  "phase_eutectic_solid_solution".

Definition calphad_hull_channel_tag : string := "calphad_hull".

Definition phase_edge_channel_tag : string := "second_law_presentation".

Lemma phase_eutectic_solid_solution_factor_tag_nonempty :
  phase_eutectic_solid_solution_factor_tag <> "".
Proof. discriminate. Qed.

Lemma calphad_hull_channel_tag_nonempty :
  calphad_hull_channel_tag <> "".
Proof. discriminate. Qed.

Lemma phase_edge_channel_tag_nonempty :
  phase_edge_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive pess_channel_slot : Type :=
  | pess_slot_unwired
  | pess_slot_absent
  | pess_slot_present.

Definition pess_channel_slot_beq (s1 s2 : pess_channel_slot) : bool :=
  match s1, s2 with
  | pess_slot_unwired, pess_slot_unwired => true
  | pess_slot_absent, pess_slot_absent => true
  | pess_slot_present, pess_slot_present => true
  | _, _ => false
  end.

Definition pess_channel_slot_is_present (s : pess_channel_slot) : bool :=
  match s with
  | pess_slot_present => true
  | _ => false
  end.

Definition phaseEutecticSolidSolutionProductChannelCount : nat := 3.

Lemma phase_eutectic_solid_solution_product_channel_count_is_three :
  phaseEutecticSolidSolutionProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = CALPHAD hull, 1 = phase edge morphism, 2 = class 13. *)
Definition pess_channel_calphad_hull : nat := 0.
Definition pess_channel_phase_edge : nat := 1.
Definition pess_channel_class13_phase_eutectic_solid_solution : nat := 2.

Lemma pess_channel_calphad_hull_idx_is_0 :
  pess_channel_calphad_hull = 0.
Proof. reflexivity. Qed.

Lemma pess_channel_phase_edge_idx_is_1 :
  pess_channel_phase_edge = 1.
Proof. reflexivity. Qed.

Lemma pess_channel_class13_phase_eutectic_solid_solution_idx_is_2 :
  pess_channel_class13_phase_eutectic_solid_solution = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition pess_channel_bundle : Type := nat -> pess_channel_slot.

Definition phaseEutecticSolidSolutionBundleAllUnwired : pess_channel_bundle :=
  fun _ => pess_slot_unwired.

Definition phaseEutecticSolidSolutionBundleAt (b : pess_channel_bundle) (idx : nat)
  (slot : pess_channel_slot) : pess_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition phaseEutecticSolidSolutionBundleWithPresent
  (b : pess_channel_bundle) (idx : nat) : pess_channel_bundle :=
  phaseEutecticSolidSolutionBundleAt b idx pess_slot_present.

Fixpoint count_pess_present_up_to (b : pess_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if pess_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_pess_present_up_to b i + add
  end.

Definition phaseEutecticSolidSolutionBundlePresentCount (b : pess_channel_bundle) : nat :=
  count_pess_present_up_to b phaseEutecticSolidSolutionProductChannelCount.

Definition phaseEutecticSolidSolutionBundleHolds (b : pess_channel_bundle) (idx : nat) : bool :=
  pess_channel_slot_is_present (b idx).

Definition phaseEutecticSolidSolutionBundleIsConcurrentProduct (b : pess_channel_bundle) : bool :=
  Nat.leb 2 (phaseEutecticSolidSolutionBundlePresentCount b).

(* Fe Z=26 CALPHAD hull G(T,P,x) + phase edge + class-13 phase eutectic solid solution concurrent witness. *)
Definition phaseEutecticSolidSolutionFe26Witness : pess_channel_bundle :=
  phaseEutecticSolidSolutionBundleWithPresent
    (phaseEutecticSolidSolutionBundleWithPresent
      (phaseEutecticSolidSolutionBundleWithPresent phaseEutecticSolidSolutionBundleAllUnwired
        pess_channel_calphad_hull)
      pess_channel_phase_edge)
    pess_channel_class13_phase_eutectic_solid_solution.

Definition phaseEutecticSolidSolutionEmptyWitness : pess_channel_bundle :=
  phaseEutecticSolidSolutionBundleAllUnwired.

Definition phaseEutecticSolidSolutionSinglePresent : pess_channel_bundle :=
  phaseEutecticSolidSolutionBundleWithPresent phaseEutecticSolidSolutionBundleAllUnwired
    pess_channel_calphad_hull.

Lemma calphad_hull_channel_present :
  phaseEutecticSolidSolutionBundleHolds phaseEutecticSolidSolutionFe26Witness
    pess_channel_calphad_hull = true.
Proof. reflexivity. Qed.

Lemma phase_edge_channel_present :
  phaseEutecticSolidSolutionBundleHolds phaseEutecticSolidSolutionFe26Witness
    pess_channel_phase_edge = true.
Proof. reflexivity. Qed.

Lemma class13_phase_eutectic_solid_solution_channel_present :
  phaseEutecticSolidSolutionBundleHolds phaseEutecticSolidSolutionFe26Witness
    pess_channel_class13_phase_eutectic_solid_solution = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  phaseEutecticSolidSolutionBundlePresentCount phaseEutecticSolidSolutionFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionFe26Witness = true.
Proof.
  unfold phaseEutecticSolidSolutionBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  phaseEutecticSolidSolutionBundlePresentCount phaseEutecticSolidSolutionEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionEmptyWitness = false.
Proof.
  unfold phaseEutecticSolidSolutionBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  phaseEutecticSolidSolutionBundlePresentCount phaseEutecticSolidSolutionSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionSinglePresent = false.
Proof.
  unfold phaseEutecticSolidSolutionBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive pess_xor_posture : Type :=
  | pess_xor_exclusive
  | pess_xor_concurrent_product.

Definition pessXorClassifierMarker : string := "chem_l0_phase_eutectic_solid_solution_xor_classifier_v1".
Definition pessConcurrentProductMarker : string := "chem_int_phase_eutectic_solid_solution_product_v1".

Lemma pess_xor_marker_ne_concurrent_product_marker :
  pessXorClassifierMarker <> pessConcurrentProductMarker.
Proof. discriminate. Qed.

Definition pessXorClassifierIncompatible (claim_xor : bool)
  (b : pess_channel_bundle) : bool :=
  claim_xor && phaseEutecticSolidSolutionBundleIsConcurrentProduct b.

Lemma pess_xor_refuse_on_fe26_witness :
  pessXorClassifierIncompatible true phaseEutecticSolidSolutionFe26Witness = true.
Proof.
  unfold pessXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma pess_xor_ok_on_concurrent_product_claim :
  pessXorClassifierIncompatible false phaseEutecticSolidSolutionFe26Witness = false.
Proof. reflexivity. Qed.

Definition pessProductNotXor : bool :=
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionFe26Witness &&
  pessXorClassifierIncompatible true phaseEutecticSolidSolutionFe26Witness.

Lemma pess_product_not_xor_true : pessProductNotXor = true.
Proof.
  unfold pessProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  pessProductNotXor = true /\
  Nat.leb 2 (phaseEutecticSolidSolutionBundlePresentCount
    phaseEutecticSolidSolutionFe26Witness) = true /\
  pessXorClassifierMarker <> pessConcurrentProductMarker.
Proof.
  split.
  - apply pess_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply pess_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive pess_bar_presence : Type :=
  | pess_bar_absent
  | pess_bar_present.

Record pess_claim_bar : Type := {
  pess_bar_presence_field : pess_bar_presence;
  pess_bar_defect_total : nat
}.

Definition phaseEutecticSolidSolutionClaimBarAbsent : pess_claim_bar :=
  {| pess_bar_presence_field := pess_bar_absent;
     pess_bar_defect_total := 0 |}.

Definition phaseEutecticSolidSolutionClaimBarZeroDefect : pess_claim_bar :=
  {| pess_bar_presence_field := pess_bar_present;
     pess_bar_defect_total := 0 |}.

Definition pess_claim_bar_zero_defect (b : pess_claim_bar) : bool :=
  match pess_bar_presence_field b with
  | pess_bar_absent => false
  | pess_bar_present => Nat.eqb (pess_bar_defect_total b) 0
  end.

Lemma pess_claim_bar_zero_defect_true :
  pess_claim_bar_zero_defect phaseEutecticSolidSolutionClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma pess_claim_bar_absent_not_zero_defect :
  pess_claim_bar_zero_defect phaseEutecticSolidSolutionClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive pess_conservation_verdict : Type :=
  | pess_verdict_unwired_ok
  | pess_verdict_named_ok
  | pess_verdict_design_ok
  | pess_verdict_trivial_refuse
  | pess_verdict_xor_refuse
  | pess_verdict_green_invent_refuse
  | pess_verdict_proved_without_bar_refuse
  | pess_verdict_production_wired_refuse
  | pess_verdict_parallel_phase_eutectic_solid_solution_axiom_refuse
  | pess_verdict_species_id_smuggle_refuse
  | pess_verdict_extra_element_id_refuse
  | pess_verdict_line_compound_smuggle_refuse
  | pess_verdict_phase_diagram_axiom_refuse
  | pess_verdict_tp_float_pin_refuse.

Definition pess_conservation_verdict_ok (v : pess_conservation_verdict) : bool :=
  match v with
  | pess_verdict_unwired_ok => true
  | pess_verdict_named_ok => true
  | pess_verdict_design_ok => true
  | _ => false
  end.

Definition phaseEutecticSolidSolutionBundleNontrivial (b : pess_channel_bundle) : bool :=
  Nat.ltb 0 (phaseEutecticSolidSolutionBundlePresentCount b).

Definition evaluate_phase_eutectic_solid_solution_bundle
  (m : PhaseEutecticSolidSolutionConservationModality)
  (b : pess_channel_bundle)
  (bar : pess_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_phase_diagram_axiom : bool) : pess_conservation_verdict :=
  if claim_physics_green
  then pess_verdict_green_invent_refuse
  else if claim_phase_diagram_axiom
       then pess_verdict_phase_diagram_axiom_refuse
       else if claim_proved
       then pess_verdict_proved_without_bar_refuse
       else if negb (phaseEutecticSolidSolutionBundleNontrivial b)
            then pess_verdict_trivial_refuse
            else if pessXorClassifierIncompatible claim_xor_classifier b
                 then pess_verdict_xor_refuse
                 else
                   match m with
                   | phase_eutectic_solid_solution_conservation_unwired =>
                       if phaseEutecticSolidSolutionBundleIsConcurrentProduct b
                       then pess_verdict_named_ok
                       else pess_verdict_design_ok
                   | phase_eutectic_solid_solution_conservation_assumed
                   | phase_eutectic_solid_solution_conservation_surrogate =>
                       pess_verdict_design_ok
                   | phase_eutectic_solid_solution_conservation_proved =>
                       pess_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_phase_eutectic_solid_solution_conservation_close
  (m : PhaseEutecticSolidSolutionConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : pess_conservation_verdict :=
  if claim_physics_green
  then pess_verdict_green_invent_refuse
  else if claim_production_wired
  then pess_verdict_production_wired_refuse
  else
    match m with
    | phase_eutectic_solid_solution_conservation_unwired => pess_verdict_unwired_ok
    | phase_eutectic_solid_solution_conservation_assumed
    | phase_eutectic_solid_solution_conservation_proved
    | phase_eutectic_solid_solution_conservation_surrogate => pess_verdict_named_ok
    end.

Definition phase_eutectic_solid_solution_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_phase_eutectic_solid_solution_conservation_close
          phase_eutectic_solid_solution_conservation_proved claim_physics_green claim_production_wired with
  | pess_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive pess_conservation_law : Type :=
  | pess_law_conserved
  | pess_law_named_ok
  | pess_law_trivial_refuse
  | pess_law_green_invent_refuse.

Definition pess_conservation_law_count : nat := 4.

Lemma pess_conservation_law_count_is_four :
  pess_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive pess_conservation_law_witness : Type :=
  | pess_law_witness_open
  | pess_law_witness_proved.

Definition evaluate_pess_conservation_law_witness
  (law : pess_conservation_law)
  (m : PhaseEutecticSolidSolutionConservationModality)
  : pess_conservation_law_witness :=
  match m with
  | phase_eutectic_solid_solution_conservation_unwired
  | phase_eutectic_solid_solution_conservation_assumed
  | phase_eutectic_solid_solution_conservation_surrogate => pess_law_witness_open
  | phase_eutectic_solid_solution_conservation_proved => pess_law_witness_proved
  end.

Lemma all_pess_conservation_laws_open_at_unwired :
  evaluate_pess_conservation_law_witness pess_law_conserved
    phase_eutectic_solid_solution_conservation_unwired = pess_law_witness_open /\
  evaluate_pess_conservation_law_witness pess_law_named_ok
    phase_eutectic_solid_solution_conservation_unwired = pess_law_witness_open /\
  evaluate_pess_conservation_law_witness pess_law_trivial_refuse
    phase_eutectic_solid_solution_conservation_unwired = pess_law_witness_open /\
  evaluate_pess_conservation_law_witness pess_law_green_invent_refuse
    phase_eutectic_solid_solution_conservation_unwired = pess_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-13 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition phaseEutecticSolidSolutionConservationProved : bool := false.

Lemma phase_eutectic_solid_solution_conservation_proved_false :
  phaseEutecticSolidSolutionConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_unwired false false =
  pess_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_unwired false false =
  pess_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_unwired false false) =
  true.
Proof.
  unfold pess_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
  pess_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_phase_eutectic_solid_solution_conservation :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
  pess_verdict_named_ok /\
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_phase_eutectic_solid_solution_idx = 13.
Proof.
  repeat split; reflexivity.
Qed.

Lemma pess_named_close_ok :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_proved false false =
  pess_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_phase_eutectic_solid_solution_conservation_close :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_proved false false =
  pess_verdict_named_ok /\
  phase_eutectic_solid_solution_conservation_authorized false false = true.
Proof.
  split.
  - apply pess_named_close_ok.
  - unfold phase_eutectic_solid_solution_conservation_authorized.
    rewrite pess_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — phase-eutectic-solid-solution refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionEmptyWitness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
  pess_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionEmptyWitness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
  pess_verdict_trivial_refuse /\
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_bundle
       phase_eutectic_solid_solution_conservation_unwired
       phaseEutecticSolidSolutionEmptyWitness
       phaseEutecticSolidSolutionClaimBarAbsent false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold pess_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent true false false false =
  pess_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent true false false false =
  pess_verdict_xor_refuse /\
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_bundle
       phase_eutectic_solid_solution_conservation_unwired
       phaseEutecticSolidSolutionFe26Witness
       phaseEutecticSolidSolutionClaimBarAbsent true false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold pess_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_unwired true false =
  pess_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_unwired true false) =
  false.
Proof.
  unfold pess_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_pess_bundle_refuse :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false true false false =
  pess_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — phase-eutectic-solid-solution refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false true false =
  pess_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false true false =
  pess_verdict_proved_without_bar_refuse /\
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_bundle
       phase_eutectic_solid_solution_conservation_unwired
       phaseEutecticSolidSolutionFe26Witness
       phaseEutecticSolidSolutionClaimBarAbsent false false true false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold pess_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — phase-eutectic-solid-solution lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_proved false true =
  pess_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_proved false true) =
  false.
Proof.
  unfold pess_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel phase-eutectic-solid-solution axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition phaseEutecticSolidSolutionConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs".

Definition parallelPhaseEutecticSolidSolutionAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_phase_eutectic_solid_solution_axiom_refuse :
  phaseEutecticSolidSolutionConservationAuthority <>
  parallelPhaseEutecticSolidSolutionAxiomTag /\
  phaseEutecticSolidSolutionConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply phase_eutectic_solid_solution_conservation_proved_false.
Qed.

Theorem parallel_phase_eutectic_solid_solution_axiom_not_minted :
  phaseEutecticSolidSolutionConservationAuthority =
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs" /\
  phaseEutecticSolidSolutionConservationProved = false /\
  phaseEutecticSolidSolutionConservationAuthority <> parallelPhaseEutecticSolidSolutionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — CALPHAD hull ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition phaseEutecticSolidSolutionConservationFraming : string :=
  "second_law_conservation_phase_eutectic_solid_solution_one_axiom".

Lemma species_id_smuggle_refuse :
  phaseEutecticSolidSolutionConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_phase_eutectic_solid_solution_idx = 13.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem calphad_hull_not_species_id_smuggle :
  phaseEutecticSolidSolutionConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_phase_eutectic_solid_solution_idx = 13 /\
  phaseEutecticSolidSolutionConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — phase eutectic solid solution ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  phaseEutecticSolidSolutionConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem phase_eutectic_not_extra_element_id :
  phaseEutecticSolidSolutionConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Line-compound smuggle refuse — line compound ≠ all solids           *)
(* ------------------------------------------------------------------ *)

Definition lineCompoundSmuggleFraming : string :=
  "line_compound_smuggle_on_all_solids_stoichiometric".

Definition phaseEdgeAuthority : string :=
  "umst/umst-chem/src/phase_eutectic_nonstoich.rs".

Lemma line_compound_smuggle_refuse :
  phaseEutecticSolidSolutionConservationFraming <>
  lineCompoundSmuggleFraming /\
  phaseEdgeAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem phase_eutectic_solid_solution_not_line_compound_smuggle :
  phaseEutecticSolidSolutionConservationFraming <>
  lineCompoundSmuggleFraming /\
  phaseEdgeAuthority =
  "umst/umst-chem/src/phase_eutectic_nonstoich.rs" /\
  phaseEutecticSolidSolutionConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  Phase-diagram axiom refuse — CALPHAD prior art not new axiom        *)
(* ------------------------------------------------------------------ *)

Definition phaseDiagramAxiomFraming : string :=
  "phase_diagram_axiom_mint_on_calphad_prior_art".

Definition calphadPriorArtAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Lemma phase_diagram_axiom_refuse :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false false true =
  pess_verdict_phase_diagram_axiom_refuse.
Proof. reflexivity. Qed.

Theorem phase_diagram_axiom_not_minted_fail_closed :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false false true =
  pess_verdict_phase_diagram_axiom_refuse /\
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_bundle
       phase_eutectic_solid_solution_conservation_unwired
       phaseEutecticSolidSolutionFe26Witness
       phaseEutecticSolidSolutionClaimBarAbsent false false false true) =
  false.
Proof.
  split.
  - apply phase_diagram_axiom_refuse.
  - unfold pess_conservation_verdict_ok.
    rewrite phase_diagram_axiom_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_phase_eutectic_solid_solution_scaffold".

Lemma tp_float_pin_refuse :
  phaseEutecticSolidSolutionConservationFraming <>
  tpFloatPinFraming /\
  calphad_hull_channel_tag = "calphad_hull".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  phaseEutecticSolidSolutionConservationFraming <>
  tpFloatPinFraming /\
  phase_edge_channel_tag = "second_law_presentation" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Phase-eutectic-solid-solution **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition pess_conservation_coherence_scaffold : bool :=
  pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_proved false false) &&
  negb (pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_unwired true false)) &&
  negb (pess_conservation_verdict_ok
    (evaluate_phase_eutectic_solid_solution_conservation_close
       phase_eutectic_solid_solution_conservation_proved false true)).

Lemma pess_conservation_coherence_scaffold_true :
  pess_conservation_coherence_scaffold = true.
Proof.
  unfold pess_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem pess_conservation_coherence_scaffold_theorem :
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_proved false false =
    pess_verdict_named_ok /\
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_unwired true false =
    pess_verdict_green_invent_refuse /\
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_proved false true =
    pess_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition pess_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition pess_conservation_knowing_fiber_ok : bool :=
  pess_conservation_fiber_ok fiber_quantum_knowing.

Definition pess_conservation_meso_acting_ok : bool :=
  pess_conservation_fiber_ok fiber_meso_acting.

Lemma pess_conservation_knowing_fiber_ok_true :
  pess_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma pess_conservation_meso_acting_not_ok :
  pess_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem pess_conservation_routes_knowing_not_meso :
  pess_conservation_knowing_fiber_ok = true /\
  pess_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply pess_conservation_knowing_fiber_ok_true.
  - apply pess_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  pess_conservation_knowing_fiber_ok &&
  negb pess_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, pess_conservation_knowing_fiber_ok,
    pess_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-13 + fail-closed + fiber               *)
(* ------------------------------------------------------------------ *)

Theorem phase_eutectic_solid_solution_conservation_fixture_scaffold :
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
    pess_verdict_named_ok /\
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionEmptyWitness
    phaseEutecticSolidSolutionClaimBarAbsent false false false false =
    pess_verdict_trivial_refuse /\
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent true false false false =
    pess_verdict_xor_refuse /\
  evaluate_phase_eutectic_solid_solution_bundle
    phase_eutectic_solid_solution_conservation_unwired
    phaseEutecticSolidSolutionFe26Witness
    phaseEutecticSolidSolutionClaimBarAbsent false false true false =
    pess_verdict_proved_without_bar_refuse /\
  evaluate_phase_eutectic_solid_solution_conservation_close
    phase_eutectic_solid_solution_conservation_unwired false false =
    pess_verdict_unwired_ok /\
  pess_conservation_knowing_fiber_ok = true /\
  pess_conservation_meso_acting_ok = false /\
  phaseEutecticSolidSolutionConservationProved = false /\
  pessProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — phase eutectic solid solution) *)
(* ------------------------------------------------------------------ *)

Definition chemL0PhaseEutecticSolidSolutionAuthority : string :=
  "umst/umst-chem/src/phase_eutectic_solid_solution.rs".

Definition chemL0PhaseEutecticSolidSolutionTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs".

Definition calphadKineticsAuthority : string :=
  "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs".

Definition thermoGTypeAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgePhaseCellId : string := "CHEM-L0-EDGE-PHASE".

Definition phaseEutecticSolidSolutionConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION".

Definition phaseEutecticSolidSolutionConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION PhaseEutecticSolidSolutionConservationModality Unwired Assumed Proved Surrogate four-step lattice phaseEutecticSolidSolutionConservationProved false evaluatePhaseEutecticSolidSolutionBundle evaluatePhaseEutecticSolidSolutionConservation named class 13 phase_eutectic_solid_solution Fe Z=26 CALPHAD hull second law phase edge morphism concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel phase eutectic solid solution axiom refuse species id smuggle refuse extra element id Z=119 refuse line compound smuggle refuse phase diagram axiom refuse phase eutectic solid solution ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma phase_eutectic_solid_solution_conservation_cell_id :
  phaseEutecticSolidSolutionConservationCellId =
  "CHEM-FORMAL-Q-COQ-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION".
Proof. reflexivity. Qed.

Lemma phase_eutectic_solid_solution_conservation_cites_l0_table :
  chemL0PhaseEutecticSolidSolutionTableAuthority <> "".
Proof. discriminate. Qed.

Lemma phase_eutectic_solid_solution_conservation_authority_path :
  phaseEutecticSolidSolutionConservationAuthority =
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs".
Proof. reflexivity. Qed.

Lemma phase_eutectic_solid_solution_conservation_cites_l0_ore02 :
  chemL0PhaseEutecticSolidSolutionAuthority <> "".
Proof. discriminate. Qed.

Lemma phase_eutectic_solid_solution_conservation_cites_marker :
  pessConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma phase_eutectic_solid_solution_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma phase_eutectic_solid_solution_conservation_cites_ore02_cell :
  chemL0EdgePhaseCellId = "CHEM-L0-EDGE-PHASE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma phase_eutectic_solid_solution_not_26th_axiom :
  phaseEutecticSolidSolutionConservationFraming <> parallelPhaseEutecticSolidSolutionAxiomTag.
Proof. discriminate. Qed.

Lemma phase_eutectic_solid_solution_second_law_conservation_framing :
  phaseEutecticSolidSolutionConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma phase_eutectic_solid_solution_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma phase_eutectic_solid_solution_conservation_modality_unwired :
  phaseEutecticSolidSolutionConservationModalityCurrent =
  phase_eutectic_solid_solution_conservation_unwired.
Proof. reflexivity. Qed.

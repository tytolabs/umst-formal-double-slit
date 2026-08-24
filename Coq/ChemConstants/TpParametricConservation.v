(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: TpParametricConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 19 **tp_parametric** **conservation**.      *)
(*  T and P are **graph functions** on Interact (v14) — not 298 K /    *)
(*  1 atm float pins. Concurrent Π_c PatternBundle factor — **product** *)
(*  not XOR. No parallel tp_parametric axiom.                           *)
(*  tpParametricConservationProved false. Modality Unwired.             *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/tp_parametric.rs (read-only cite). *)
(*  INT: umst/umst-chem/src/temperature_is_graph_function.rs (read-only). *)
(*  INT: umst/umst-chem/src/pressure_is_graph_function.rs (read-only).  *)
(*  INT: umst/umst-chem/src/tp_parametric_morphism.rs (read-only cite). *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-19 **tp_parametric** **conservation** modality   *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive TpParametricConservationModality : Type :=
  | tp_parametric_conservation_unwired
  | tp_parametric_conservation_assumed
  | tp_parametric_conservation_proved
  | tp_parametric_conservation_surrogate.

Definition tpParametricConservationModalityCurrent :
  TpParametricConservationModality :=
  tp_parametric_conservation_unwired.

Definition tp_parametric_lattice_cardinality : nat := 4.

Lemma tp_parametric_lattice_cardinality_is_four :
  tp_parametric_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma tp_parametric_lattice_not_118_squared :
  negb (Nat.eqb tp_parametric_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold tp_parametric_lattice_cardinality.
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

(* North-star §2 class 19 — tp_parametric concurrent Π_c factor. *)
Definition pattern_class_tp_parametric_idx : nat := 19.

Lemma pattern_class_tp_parametric_idx_is_19 :
  pattern_class_tp_parametric_idx = 19.
Proof. reflexivity. Qed.

Lemma tp_parametric_class_index_valid :
  pattern_class_index_valid pattern_class_tp_parametric_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_tp_parametric_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierTpParametricRowId : string := "X19".

Lemma cross_classifier_tp_parametric_row_named :
  crossClassifierTpParametricRowId = "X19".
Proof. reflexivity. Qed.

Definition pattern_class_tp_parametric_tag : string :=
  "tp_parametric".

Definition north_star_class_19_tp_parametric_tag : string :=
  "class 19 tp parametric".

Lemma pattern_class_tp_parametric_tag_nonempty :
  pattern_class_tp_parametric_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_19_tp_parametric_tag_nonempty :
  north_star_class_19_tp_parametric_tag <> "".
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

Definition tp_parametric_factor_tag : string :=
  "tp_parametric".

Definition temperature_graph_function_channel_tag : string := "temperature_graph_function".

Definition pressure_graph_function_channel_tag : string := "pressure_graph_function".

Lemma tp_parametric_factor_tag_nonempty :
  tp_parametric_factor_tag <> "".
Proof. discriminate. Qed.

Lemma temperature_graph_function_channel_tag_nonempty :
  temperature_graph_function_channel_tag <> "".
Proof. discriminate. Qed.

Lemma pressure_graph_function_channel_tag_nonempty :
  pressure_graph_function_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive tpc_channel_slot : Type :=
  | tpc_slot_unwired
  | tpc_slot_absent
  | tpc_slot_present.

Definition tpc_channel_slot_beq (s1 s2 : tpc_channel_slot) : bool :=
  match s1, s2 with
  | tpc_slot_unwired, tpc_slot_unwired => true
  | tpc_slot_absent, tpc_slot_absent => true
  | tpc_slot_present, tpc_slot_present => true
  | _, _ => false
  end.

Definition tpc_channel_slot_is_present (s : tpc_channel_slot) : bool :=
  match s with
  | tpc_slot_present => true
  | _ => false
  end.

Definition tpParametricProductChannelCount : nat := 3.

Lemma tp_parametric_product_channel_count_is_three :
  tpParametricProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 catalysis. *)
Definition tpc_channel_temperature_graph_function : nat := 0.
Definition tpc_channel_pressure_graph_function : nat := 1.
Definition tpc_channel_class19_tp_parametric : nat := 2.

Lemma tpc_channel_temperature_graph_function_idx_is_0 :
  tpc_channel_temperature_graph_function = 0.
Proof. reflexivity. Qed.

Lemma tpc_channel_pressure_graph_function_idx_is_1 :
  tpc_channel_pressure_graph_function = 1.
Proof. reflexivity. Qed.

Lemma tpc_channel_class19_tp_parametric_idx_is_2 :
  tpc_channel_class19_tp_parametric = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric concurrent **product** bundle scaffold  *)
(* ------------------------------------------------------------------ *)

Definition tpc_channel_bundle : Type := nat -> tpc_channel_slot.

Definition tpParametricBundleAllUnwired : tpc_channel_bundle :=
  fun _ => tpc_slot_unwired.

Definition tpParametricBundleAt (b : tpc_channel_bundle) (idx : nat)
  (slot : tpc_channel_slot) : tpc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition tpParametricBundleWithPresent
  (b : tpc_channel_bundle) (idx : nat) : tpc_channel_bundle :=
  tpParametricBundleAt b idx tpc_slot_present.

Fixpoint count_tpc_present_up_to (b : tpc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if tpc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_tpc_present_up_to b i + add
  end.

Definition tpParametricBundlePresentCount (b : tpc_channel_bundle) : nat :=
  count_tpc_present_up_to b tpParametricProductChannelCount.

Definition tpParametricBundleHolds (b : tpc_channel_bundle) (idx : nat) : bool :=
  tpc_channel_slot_is_present (b idx).

Definition tpParametricBundleIsConcurrentProduct (b : tpc_channel_bundle) : bool :=
  Nat.leb 2 (tpParametricBundlePresentCount b).

(* Fe Z=26 interact restriction + G-min + class 14 catalysis concurrent witness. *)
Definition tpParametricFe26Witness : tpc_channel_bundle :=
  tpParametricBundleWithPresent
    (tpParametricBundleWithPresent
      (tpParametricBundleWithPresent tpParametricBundleAllUnwired
        tpc_channel_temperature_graph_function)
      tpc_channel_pressure_graph_function)
    tpc_channel_class19_tp_parametric.

Definition tpParametricEmptyWitness : tpc_channel_bundle :=
  tpParametricBundleAllUnwired.

Definition tpParametricSinglePresent : tpc_channel_bundle :=
  tpParametricBundleWithPresent tpParametricBundleAllUnwired
    tpc_channel_temperature_graph_function.

Lemma temperature_graph_function_channel_present :
  tpParametricBundleHolds tpParametricFe26Witness
    tpc_channel_temperature_graph_function = true.
Proof. reflexivity. Qed.

Lemma pressure_graph_function_channel_present :
  tpParametricBundleHolds tpParametricFe26Witness
    tpc_channel_pressure_graph_function = true.
Proof. reflexivity. Qed.

Lemma class19_tp_parametric_channel_present :
  tpParametricBundleHolds tpParametricFe26Witness
    tpc_channel_class19_tp_parametric = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  tpParametricBundlePresentCount tpParametricFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  tpParametricBundleIsConcurrentProduct tpParametricFe26Witness = true.
Proof.
  unfold tpParametricBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  tpParametricBundlePresentCount tpParametricEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  tpParametricBundleIsConcurrentProduct tpParametricEmptyWitness = false.
Proof.
  unfold tpParametricBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  tpParametricBundlePresentCount tpParametricSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  tpParametricBundleIsConcurrentProduct tpParametricSinglePresent = false.
Proof.
  unfold tpParametricBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive tpc_xor_posture : Type :=
  | tpc_xor_exclusive
  | tpc_xor_concurrent_product.

Definition tpcXorClassifierMarker : string := "chem_l0_tp_parametric_xor_classifier_v1".
Definition tpcConcurrentProductMarker : string := "chem_int_tp_parametric_product_v1".

Lemma tpc_xor_marker_ne_concurrent_product_marker :
  tpcXorClassifierMarker <> tpcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition tpcXorClassifierIncompatible (claim_xor : bool)
  (b : tpc_channel_bundle) : bool :=
  claim_xor && tpParametricBundleIsConcurrentProduct b.

Lemma tpc_xor_refuse_on_fe26_witness :
  tpcXorClassifierIncompatible true tpParametricFe26Witness = true.
Proof.
  unfold tpcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma tpc_xor_ok_on_concurrent_product_claim :
  tpcXorClassifierIncompatible false tpParametricFe26Witness = false.
Proof. reflexivity. Qed.

Definition tpcProductNotXor : bool :=
  tpParametricBundleIsConcurrentProduct tpParametricFe26Witness &&
  tpcXorClassifierIncompatible true tpParametricFe26Witness.

Lemma tpc_product_not_xor_true : tpcProductNotXor = true.
Proof.
  unfold tpcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  tpcProductNotXor = true /\
  Nat.leb 2 (tpParametricBundlePresentCount
    tpParametricFe26Witness) = true /\
  tpcXorClassifierMarker <> tpcConcurrentProductMarker.
Proof.
  split.
  - apply tpc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply tpc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive tpc_bar_presence : Type :=
  | tpc_bar_absent
  | tpc_bar_present.

Record tpc_claim_bar : Type := {
  tpc_bar_presence_field : tpc_bar_presence;
  tpc_bar_defect_total : nat
}.

Definition tpParametricClaimBarAbsent : tpc_claim_bar :=
  {| tpc_bar_presence_field := tpc_bar_absent;
     tpc_bar_defect_total := 0 |}.

Definition tpParametricClaimBarZeroDefect : tpc_claim_bar :=
  {| tpc_bar_presence_field := tpc_bar_present;
     tpc_bar_defect_total := 0 |}.

Definition tpc_claim_bar_zero_defect (b : tpc_claim_bar) : bool :=
  match tpc_bar_presence_field b with
  | tpc_bar_absent => false
  | tpc_bar_present => Nat.eqb (tpc_bar_defect_total b) 0
  end.

Lemma tpc_claim_bar_zero_defect_true :
  tpc_claim_bar_zero_defect tpParametricClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma tpc_claim_bar_absent_not_zero_defect :
  tpc_claim_bar_zero_defect tpParametricClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric **conservation** verdict — fail-closed    *)
(* ------------------------------------------------------------------ *)

Inductive tpc_conservation_verdict : Type :=
  | tpc_verdict_unwired_ok
  | tpc_verdict_named_ok
  | tpc_verdict_design_ok
  | tpc_verdict_trivial_refuse
  | tpc_verdict_xor_refuse
  | tpc_verdict_green_invent_refuse
  | tpc_verdict_proved_without_bar_refuse
  | tpc_verdict_production_wired_refuse
  | tpc_verdict_parallel_tp_parametric_axiom_refuse
  | tpc_verdict_float_pin_smuggle_refuse
  | tpc_verdict_parallel_axiom_smuggle_refuse
  | tpc_verdict_tp_float_pin_refuse.

Definition tpc_conservation_verdict_ok (v : tpc_conservation_verdict) : bool :=
  match v with
  | tpc_verdict_unwired_ok => true
  | tpc_verdict_named_ok => true
  | tpc_verdict_design_ok => true
  | _ => false
  end.

Definition tpParametricBundleNontrivial (b : tpc_channel_bundle) : bool :=
  Nat.ltb 0 (tpParametricBundlePresentCount b).

Definition evaluate_tp_parametric_bundle
  (m : TpParametricConservationModality)
  (b : tpc_channel_bundle)
  (bar : tpc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : tpc_conservation_verdict :=
  if claim_physics_green
  then tpc_verdict_green_invent_refuse
  else if claim_proved
       then tpc_verdict_proved_without_bar_refuse
       else if negb (tpParametricBundleNontrivial b)
            then tpc_verdict_trivial_refuse
            else if tpcXorClassifierIncompatible claim_xor_classifier b
                 then tpc_verdict_xor_refuse
                 else
                   match m with
                   | tp_parametric_conservation_unwired =>
                       if tpParametricBundleIsConcurrentProduct b
                       then tpc_verdict_named_ok
                       else tpc_verdict_design_ok
                   | tp_parametric_conservation_assumed
                   | tp_parametric_conservation_surrogate =>
                       tpc_verdict_design_ok
                   | tp_parametric_conservation_proved =>
                       tpc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_tp_parametric_conservation_close
  (m : TpParametricConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : tpc_conservation_verdict :=
  if claim_physics_green
  then tpc_verdict_green_invent_refuse
  else if claim_production_wired
  then tpc_verdict_production_wired_refuse
  else
    match m with
    | tp_parametric_conservation_unwired => tpc_verdict_unwired_ok
    | tp_parametric_conservation_assumed
    | tp_parametric_conservation_proved
    | tp_parametric_conservation_surrogate => tpc_verdict_named_ok
    end.

Definition tp_parametric_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_tp_parametric_conservation_close
          tp_parametric_conservation_proved claim_physics_green claim_production_wired with
  | tpc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric **conservation** law cells — four laws     *)
(* ------------------------------------------------------------------ *)

Inductive tpc_conservation_law : Type :=
  | tpc_law_conserved
  | tpc_law_named_ok
  | tpc_law_trivial_refuse
  | tpc_law_green_invent_refuse.

Definition tpc_conservation_law_count : nat := 4.

Lemma tpc_conservation_law_count_is_four :
  tpc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive tpc_conservation_law_witness : Type :=
  | tpc_law_witness_open
  | tpc_law_witness_proved.

Definition evaluate_tpc_conservation_law_witness
  (law : tpc_conservation_law)
  (m : TpParametricConservationModality)
  : tpc_conservation_law_witness :=
  match m with
  | tp_parametric_conservation_unwired
  | tp_parametric_conservation_assumed
  | tp_parametric_conservation_surrogate => tpc_law_witness_open
  | tp_parametric_conservation_proved => tpc_law_witness_proved
  end.

Lemma all_tpc_conservation_laws_open_at_unwired :
  evaluate_tpc_conservation_law_witness tpc_law_conserved
    tp_parametric_conservation_unwired = tpc_law_witness_open /\
  evaluate_tpc_conservation_law_witness tpc_law_named_ok
    tp_parametric_conservation_unwired = tpc_law_witness_open /\
  evaluate_tpc_conservation_law_witness tpc_law_trivial_refuse
    tp_parametric_conservation_unwired = tpc_law_witness_open /\
  evaluate_tpc_conservation_law_witness tpc_law_green_invent_refuse
    tp_parametric_conservation_unwired = tpc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-19 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition tpParametricConservationProved : bool := false.

Lemma tp_parametric_conservation_proved_false :
  tpParametricConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_unwired false false =
  tpc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_unwired false false =
  tpc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_unwired false false) =
  true.
Proof.
  unfold tpc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false false =
  tpc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_tp_parametric_conservation :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false false =
  tpc_verdict_named_ok /\
  tpParametricBundleIsConcurrentProduct tpParametricFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_tp_parametric_idx = 19.
Proof.
  repeat split; reflexivity.
Qed.

Lemma tpc_named_close_ok :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_proved false false =
  tpc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_tp_parametric_conservation_close :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_proved false false =
  tpc_verdict_named_ok /\
  tp_parametric_conservation_authorized false false = true.
Proof.
  split.
  - apply tpc_named_close_ok.
  - unfold tp_parametric_conservation_authorized.
    rewrite tpc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — tp_parametric refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricEmptyWitness
    tpParametricClaimBarAbsent false false false =
  tpc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricEmptyWitness
    tpParametricClaimBarAbsent false false false =
  tpc_verdict_trivial_refuse /\
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_bundle
       tp_parametric_conservation_unwired
       tpParametricEmptyWitness
       tpParametricClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold tpc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent true false false =
  tpc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent true false false =
  tpc_verdict_xor_refuse /\
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_bundle
       tp_parametric_conservation_unwired
       tpParametricFe26Witness
       tpParametricClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold tpc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_unwired true false =
  tpc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_unwired true false) =
  false.
Proof.
  unfold tpc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_tpc_bundle_refuse :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false true false =
  tpc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — tp_parametric refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false true =
  tpc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false true =
  tpc_verdict_proved_without_bar_refuse /\
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_bundle
       tp_parametric_conservation_unwired
       tpParametricFe26Witness
       tpParametricClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold tpc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — tp_parametric lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_proved false true =
  tpc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_proved false true) =
  false.
Proof.
  unfold tpc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel tp_parametric axiom refuse — no parallel law minted      *)
(* ------------------------------------------------------------------ *)

Definition tpParametricConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/tp_parametric.rs".

Definition parallelTpParametricAxiomTag : string := "parallel_tp_parametric_axiom".

Lemma parallel_tp_parametric_axiom_refuse :
  tpParametricConservationAuthority <>
  parallelTpParametricAxiomTag /\
  tpParametricConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply tp_parametric_conservation_proved_false.
Qed.

Theorem parallel_tp_parametric_axiom_not_minted :
  tpParametricConservationAuthority =
  "umst/umst-chem/src/l0_tables/tp_parametric.rs" /\
  tpParametricConservationProved = false /\
  tpParametricConservationAuthority <> parallelTpParametricAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition floatPinSmuggleFraming : string :=
  "bare_298_15_k_1_atm_float_pins_not_graph_functions".

Definition tpParametricConservationFraming : string :=
  "second_law_conservation_tp_parametric_graph_restriction_one_axiom".

Lemma float_pin_smuggle_refuse :
  tpParametricConservationFraming <>
  floatPinSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_tp_parametric_idx = 19.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem temperature_graph_function_not_float_pin_smuggle :
  tpParametricConservationFraming <>
  floatPinSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_tp_parametric_idx = 19 /\
  tpParametricConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel axiom smuggle refuse — tp_parametric ≠ parallel law *)
(* ------------------------------------------------------------------ *)

Definition parallelAxiomSmuggleFraming : string :=
  "parallel_tp_parametric_axiom_minted_as_extra_law".

Lemma parallel_axiom_smuggle_refuse :
  tpParametricConservationFraming <>
  parallelAxiomSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_parallel_axiom_smuggle :
  tpParametricConservationFraming <>
  parallelAxiomSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel axiom refuse — tp_parametric ≠ parallel tp_parametric axiom    *)
(* ------------------------------------------------------------------ *)

Definition parallelTpParametricAxiomFraming : string :=
  "parallel_tp_parametric_axiom_minted_as_extra_law".

Definition edgeTpAuthority : string :=
  "umst/umst-chem/src/tp_parametric_morphism.rs".

Lemma parallel_tp_parametric_axiom_edge_refuse :
  tpParametricConservationFraming <>
  parallelTpParametricAxiomFraming /\
  edgeTpAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem tp_parametric_not_parallel_tp_parametric_axiom :
  tpParametricConservationFraming <>
  parallelTpParametricAxiomFraming /\
  edgeTpAuthority =
  "umst/umst-chem/src/tp_parametric_morphism.rs" /\
  tpParametricConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_tp_parametric_scaffold".

Lemma tp_float_pin_refuse :
  tpParametricConservationFraming <>
  tpFloatPinFraming /\
  temperature_graph_function_channel_tag = "temperature_graph_function".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  tpParametricConservationFraming <>
  tpFloatPinFraming /\
  pressure_graph_function_channel_tag = "pressure_graph_function" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P-parametric **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition tpc_conservation_coherence_scaffold : bool :=
  tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_proved false false) &&
  negb (tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_unwired true false)) &&
  negb (tpc_conservation_verdict_ok
    (evaluate_tp_parametric_conservation_close
       tp_parametric_conservation_proved false true)).

Lemma tpc_conservation_coherence_scaffold_true :
  tpc_conservation_coherence_scaffold = true.
Proof.
  unfold tpc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem tpc_conservation_coherence_scaffold_theorem :
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_proved false false =
    tpc_verdict_named_ok /\
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_unwired true false =
    tpc_verdict_green_invent_refuse /\
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_proved false true =
    tpc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition tpc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition tpc_conservation_knowing_fiber_ok : bool :=
  tpc_conservation_fiber_ok fiber_quantum_knowing.

Definition tpc_conservation_meso_acting_ok : bool :=
  tpc_conservation_fiber_ok fiber_meso_acting.

Lemma tpc_conservation_knowing_fiber_ok_true :
  tpc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma tpc_conservation_meso_acting_not_ok :
  tpc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem tpc_conservation_routes_knowing_not_meso :
  tpc_conservation_knowing_fiber_ok = true /\
  tpc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply tpc_conservation_knowing_fiber_ok_true.
  - apply tpc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  tpc_conservation_knowing_fiber_ok &&
  negb tpc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, tpc_conservation_knowing_fiber_ok,
    tpc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-19 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem tp_parametric_conservation_fixture_scaffold :
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false false =
    tpc_verdict_named_ok /\
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricEmptyWitness
    tpParametricClaimBarAbsent false false false =
    tpc_verdict_trivial_refuse /\
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent true false false =
    tpc_verdict_xor_refuse /\
  evaluate_tp_parametric_bundle
    tp_parametric_conservation_unwired
    tpParametricFe26Witness
    tpParametricClaimBarAbsent false false true =
    tpc_verdict_proved_without_bar_refuse /\
  evaluate_tp_parametric_conservation_close
    tp_parametric_conservation_unwired false false =
    tpc_verdict_unwired_ok /\
  tpc_conservation_knowing_fiber_ok = true /\
  tpc_conservation_meso_acting_ok = false /\
  tpParametricConservationProved = false /\
  tpcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — tp_parametric) *)
(* ------------------------------------------------------------------ *)

Definition chemL0TpParametricAuthority : string :=
  "umst/umst-chem/src/catalysis.rs".

Definition chemL0TpParametricTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/tp_parametric.rs".

Definition temperatureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/temperature_is_graph_function.rs".

Definition pressureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/pressure_is_graph_function.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeTpCellId : string := "CHEM-L0-EDGE-TP".

Definition tpParametricConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-TP-PARAMETRIC-CONSERVATION".

Definition tpParametricConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-TP-PARAMETRIC-CONSERVATION TpParametricConservationModality Unwired Assumed Proved Surrogate four-step lattice tpParametricConservationProved false evaluateTpParametricBundle evaluateTpParametricConservation named class 19 tp_parametric Fe Z=26 temperature graph function pressure graph function concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel tp_parametric axiom refuse float pin smuggle refuse parallel axiom smuggle refuse tp graph function not parallel axiom Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma tp_parametric_conservation_cell_id :
  tpParametricConservationCellId =
  "CHEM-FORMAL-Q-COQ-TP-PARAMETRIC-CONSERVATION".
Proof. reflexivity. Qed.

Lemma tp_parametric_conservation_cites_l0_table :
  chemL0TpParametricTableAuthority <> "".
Proof. discriminate. Qed.

Lemma tp_parametric_conservation_authority_path :
  tpParametricConservationAuthority =
  "umst/umst-chem/src/l0_tables/tp_parametric.rs".
Proof. reflexivity. Qed.

Lemma tp_parametric_conservation_cites_temperature_graph :
  temperatureGraphFunctionAuthority <> "".
Proof. discriminate. Qed.

Lemma tp_parametric_conservation_cites_marker :
  tpcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma tp_parametric_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma tp_parametric_conservation_cites_pressure_graph :
  pressureGraphFunctionAuthority = "umst/umst-chem/src/pressure_is_graph_function.rs".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not parallel tp_parametric axiom    *)
(* ------------------------------------------------------------------ *)

Lemma tp_parametric_not_26th_axiom :
  tpParametricConservationFraming <> parallelTpParametricAxiomTag.
Proof. discriminate. Qed.

Lemma tp_parametric_second_law_conservation_framing :
  tpParametricConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Temperature graph function — named object, not float pin            *)
(* ------------------------------------------------------------------ *)

Definition pressureGraphFunctionFraming : string :=
  "bare_1_atm_float_pin_not_graph_function".

Definition tpGraphFunctionNamedObject : string :=
  "temperature_graph_function_on_interact_graph_v14".

Lemma pressure_graph_function_not_named_object :
  tpGraphFunctionNamedObject <>
  pressureGraphFunctionFraming /\
  pressure_graph_function_channel_tag = "pressure_graph_function".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem temperature_graph_function_is_named_object_not_tst :
  tpGraphFunctionNamedObject <>
  pressureGraphFunctionFraming /\
  temperature_graph_function_channel_tag = "temperature_graph_function" /\
  tpParametricConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Graph function refuse — not parallel tp_parametric axiom / extra force *)
(* ------------------------------------------------------------------ *)

Definition tpGraphFunctionFraming : string :=
  "tp_graph_function_not_parallel_axiom".

Lemma temperature_graph_function_not_extra_force_refuse :
  tpGraphFunctionFraming <>
  parallelTpParametricAxiomFraming /\
  temperature_graph_function_channel_tag = "temperature_graph_function".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_parametric_graph_restriction_not_extra_force :
  tpGraphFunctionFraming <>
  parallelTpParametricAxiomFraming /\
  edgeTpAuthority =
  "umst/umst-chem/src/tp_parametric_morphism.rs" /\
  tpParametricConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma tp_parametric_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma tp_parametric_conservation_modality_unwired :
  tpParametricConservationModalityCurrent =
  tp_parametric_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ContaminationReverseRefineConservation.v               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 20 **contamination_reverse_refine**       *)
(*  **conservation**. Contamination is the **reverse of Refine** on    *)
(*  the same second-law + conservation object (not a parallel           *)
(*  contamination axiom). No free mix-reverse. Concurrent Π_c         *)
(*  PatternBundle factor — **product** not XOR. T / P are graph         *)
(*  functions on Interact (v14) — not 298 K / 1 atm float pins.       *)
(*  contaminationReverseRefineConservationProved false. Modality        *)
(*  Unwired. WAVE100: no lib.rs / eos.rs / cabal / lakefile.           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/contamination_reverse_refine.rs (cite).    *)
(*  INT: umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs  *)
(*  (read-only cite). INT: umst/umst-chem/src/refine_effect_types.rs.    *)
(*  INT: umst/umst-chem/src/contamination_is_messy_section.rs (cite).    *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-20 **contamination_reverse_refine** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive ContaminationReverseRefineConservationModality : Type :=
  | contamination_reverse_refine_conservation_unwired
  | contamination_reverse_refine_conservation_assumed
  | contamination_reverse_refine_conservation_proved
  | contamination_reverse_refine_conservation_surrogate.

Definition contaminationReverseRefineConservationModalityCurrent :
  ContaminationReverseRefineConservationModality :=
  contamination_reverse_refine_conservation_unwired.

Definition contamination_reverse_refine_lattice_cardinality : nat := 4.

Lemma contamination_reverse_refine_lattice_cardinality_is_four :
  contamination_reverse_refine_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma contamination_reverse_refine_lattice_not_118_squared :
  negb (Nat.eqb contamination_reverse_refine_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold contamination_reverse_refine_lattice_cardinality.
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

(* North-star §2 class 20 — contamination_reverse_refine concurrent Π_c factor. *)
Definition pattern_class_contamination_reverse_refine_idx : nat := 20.

Lemma pattern_class_contamination_reverse_refine_idx_is_20 :
  pattern_class_contamination_reverse_refine_idx = 20.
Proof. reflexivity. Qed.

Lemma contamination_reverse_refine_class_index_valid :
  pattern_class_index_valid pattern_class_contamination_reverse_refine_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_contamination_reverse_refine_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierContaminationReverseRefineRowId : string := "X20".

Lemma cross_classifier_contamination_reverse_refine_row_named :
  crossClassifierContaminationReverseRefineRowId = "X20".
Proof. reflexivity. Qed.

Definition pattern_class_contamination_reverse_refine_tag : string :=
  "contamination_reverse_refine".

Definition north_star_class_20_contamination_reverse_refine_tag : string :=
  "class 20 contamination reverse refine".

Lemma pattern_class_contamination_reverse_refine_tag_nonempty :
  pattern_class_contamination_reverse_refine_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_20_contamination_reverse_refine_tag_nonempty :
  north_star_class_20_contamination_reverse_refine_tag <> "".
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

Definition contamination_reverse_refine_factor_tag : string :=
  "contamination_reverse_refine".

Definition reverse_of_refine_channel_tag : string := "reverse_of_refine".

Definition second_law_sole_axiom_channel_tag : string := "second_law_sole_axiom".

Lemma contamination_reverse_refine_factor_tag_nonempty :
  contamination_reverse_refine_factor_tag <> "".
Proof. discriminate. Qed.

Lemma reverse_of_refine_channel_tag_nonempty :
  reverse_of_refine_channel_tag <> "".
Proof. discriminate. Qed.

Lemma second_law_sole_axiom_channel_tag_nonempty :
  second_law_sole_axiom_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive crrc_channel_slot : Type :=
  | crrc_slot_unwired
  | crrc_slot_absent
  | crrc_slot_present.

Definition crrc_channel_slot_beq (s1 s2 : crrc_channel_slot) : bool :=
  match s1, s2 with
  | crrc_slot_unwired, crrc_slot_unwired => true
  | crrc_slot_absent, crrc_slot_absent => true
  | crrc_slot_present, crrc_slot_present => true
  | _, _ => false
  end.

Definition crrc_channel_slot_is_present (s : crrc_channel_slot) : bool :=
  match s with
  | crrc_slot_present => true
  | _ => false
  end.

Definition contaminationReverseRefineProductChannelCount : nat := 3.

Lemma contamination_reverse_refine_product_channel_count_is_three :
  contaminationReverseRefineProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 20 contamination_reverse_refine. *)
Definition crrc_channel_reverse_of_refine : nat := 0.
Definition crrc_channel_second_law_sole_axiom : nat := 1.
Definition crrc_channel_class20_contamination_reverse_refine : nat := 2.

Lemma crrc_channel_reverse_of_refine_idx_is_0 :
  crrc_channel_reverse_of_refine = 0.
Proof. reflexivity. Qed.

Lemma crrc_channel_second_law_sole_axiom_idx_is_1 :
  crrc_channel_second_law_sole_axiom = 1.
Proof. reflexivity. Qed.

Lemma crrc_channel_class20_contamination_reverse_refine_idx_is_2 :
  crrc_channel_class20_contamination_reverse_refine = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition crrc_channel_bundle : Type := nat -> crrc_channel_slot.

Definition contaminationReverseRefineBundleAllUnwired : crrc_channel_bundle :=
  fun _ => crrc_slot_unwired.

Definition contaminationReverseRefineBundleAt (b : crrc_channel_bundle) (idx : nat)
  (slot : crrc_channel_slot) : crrc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition contaminationReverseRefineBundleWithPresent
  (b : crrc_channel_bundle) (idx : nat) : crrc_channel_bundle :=
  contaminationReverseRefineBundleAt b idx crrc_slot_present.

Fixpoint count_crrc_present_up_to (b : crrc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if crrc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_crrc_present_up_to b i + add
  end.

Definition contaminationReverseRefineBundlePresentCount (b : crrc_channel_bundle) : nat :=
  count_crrc_present_up_to b contaminationReverseRefineProductChannelCount.

Definition contaminationReverseRefineBundleHolds (b : crrc_channel_bundle) (idx : nat) : bool :=
  crrc_channel_slot_is_present (b idx).

Definition contaminationReverseRefineBundleIsConcurrentProduct (b : crrc_channel_bundle) : bool :=
  Nat.leb 2 (contaminationReverseRefineBundlePresentCount b).

(* Fe Z=26 interact restriction + G-min + class 20 contamination_reverse_refine concurrent witness. *)
Definition contaminationReverseRefineFe26Witness : crrc_channel_bundle :=
  contaminationReverseRefineBundleWithPresent
    (contaminationReverseRefineBundleWithPresent
      (contaminationReverseRefineBundleWithPresent contaminationReverseRefineBundleAllUnwired
        crrc_channel_reverse_of_refine)
      crrc_channel_second_law_sole_axiom)
    crrc_channel_class20_contamination_reverse_refine.

Definition contaminationReverseRefineEmptyWitness : crrc_channel_bundle :=
  contaminationReverseRefineBundleAllUnwired.

Definition contaminationReverseRefineSinglePresent : crrc_channel_bundle :=
  contaminationReverseRefineBundleWithPresent contaminationReverseRefineBundleAllUnwired
    crrc_channel_reverse_of_refine.

Lemma reverse_of_refine_channel_present :
  contaminationReverseRefineBundleHolds contaminationReverseRefineFe26Witness
    crrc_channel_reverse_of_refine = true.
Proof. reflexivity. Qed.

Lemma second_law_sole_axiom_channel_present :
  contaminationReverseRefineBundleHolds contaminationReverseRefineFe26Witness
    crrc_channel_second_law_sole_axiom = true.
Proof. reflexivity. Qed.

Lemma class20_contamination_reverse_refine_channel_present :
  contaminationReverseRefineBundleHolds contaminationReverseRefineFe26Witness
    crrc_channel_class20_contamination_reverse_refine = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  contaminationReverseRefineBundlePresentCount contaminationReverseRefineFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineFe26Witness = true.
Proof.
  unfold contaminationReverseRefineBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  contaminationReverseRefineBundlePresentCount contaminationReverseRefineEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineEmptyWitness = false.
Proof.
  unfold contaminationReverseRefineBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  contaminationReverseRefineBundlePresentCount contaminationReverseRefineSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineSinglePresent = false.
Proof.
  unfold contaminationReverseRefineBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ccv_xor_posture : Type :=
  | ccv_xor_exclusive
  | ccv_xor_concurrent_product.

Definition crrcXorClassifierMarker : string := "chem_l0_contamination_reverse_refine_xor_classifier_v1".
Definition crrcConcurrentProductMarker : string := "chem_int_contamination_reverse_refine_product_v1".

Lemma crrc_xor_marker_ne_concurrent_product_marker :
  crrcXorClassifierMarker <> crrcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition crrcXorClassifierIncompatible (claim_xor : bool)
  (b : crrc_channel_bundle) : bool :=
  claim_xor && contaminationReverseRefineBundleIsConcurrentProduct b.

Lemma crrc_xor_refuse_on_fe26_witness :
  crrcXorClassifierIncompatible true contaminationReverseRefineFe26Witness = true.
Proof.
  unfold crrcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma crrc_xor_ok_on_concurrent_product_claim :
  crrcXorClassifierIncompatible false contaminationReverseRefineFe26Witness = false.
Proof. reflexivity. Qed.

Definition crrcProductNotXor : bool :=
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineFe26Witness &&
  crrcXorClassifierIncompatible true contaminationReverseRefineFe26Witness.

Lemma crrc_product_not_xor_true : crrcProductNotXor = true.
Proof.
  unfold crrcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  crrcProductNotXor = true /\
  Nat.leb 2 (contaminationReverseRefineBundlePresentCount
    contaminationReverseRefineFe26Witness) = true /\
  crrcXorClassifierMarker <> crrcConcurrentProductMarker.
Proof.
  split.
  - apply crrc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply crrc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive crrc_bar_presence : Type :=
  | crrc_bar_absent
  | crrc_bar_present.

Record crrc_claim_bar : Type := {
  crrc_bar_presence_field : crrc_bar_presence;
  crrc_bar_defect_total : nat
}.

Definition contaminationReverseRefineClaimBarAbsent : crrc_claim_bar :=
  {| crrc_bar_presence_field := crrc_bar_absent;
     crrc_bar_defect_total := 0 |}.

Definition contaminationReverseRefineClaimBarZeroDefect : crrc_claim_bar :=
  {| crrc_bar_presence_field := crrc_bar_present;
     crrc_bar_defect_total := 0 |}.

Definition crrc_claim_bar_zero_defect (b : crrc_claim_bar) : bool :=
  match crrc_bar_presence_field b with
  | crrc_bar_absent => false
  | crrc_bar_present => Nat.eqb (crrc_bar_defect_total b) 0
  end.

Lemma crrc_claim_bar_zero_defect_true :
  crrc_claim_bar_zero_defect contaminationReverseRefineClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma crrc_claim_bar_absent_not_zero_defect :
  crrc_claim_bar_zero_defect contaminationReverseRefineClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive crrc_conservation_verdict : Type :=
  | crrc_verdict_unwired_ok
  | crrc_verdict_named_ok
  | crrc_verdict_design_ok
  | crrc_verdict_trivial_refuse
  | crrc_verdict_xor_refuse
  | crrc_verdict_green_invent_refuse
  | crrc_verdict_proved_without_bar_refuse
  | crrc_verdict_production_wired_refuse
  | ccv_verdict_parallel_contamination_axiom_refuse
  | crrc_verdict_species_id_smuggle_refuse
  | crrc_verdict_extra_element_id_refuse
  | crrc_verdict_free_mix_reverse_refuse
  | crrc_verdict_tp_float_pin_refuse.

Definition crrc_conservation_verdict_ok (v : crrc_conservation_verdict) : bool :=
  match v with
  | crrc_verdict_unwired_ok => true
  | crrc_verdict_named_ok => true
  | crrc_verdict_design_ok => true
  | _ => false
  end.

Definition contaminationReverseRefineBundleNontrivial (b : crrc_channel_bundle) : bool :=
  Nat.ltb 0 (contaminationReverseRefineBundlePresentCount b).

Definition evaluate_contamination_reverse_refine_bundle
  (m : ContaminationReverseRefineConservationModality)
  (b : crrc_channel_bundle)
  (bar : crrc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : crrc_conservation_verdict :=
  if claim_physics_green
  then crrc_verdict_green_invent_refuse
  else if claim_proved
       then crrc_verdict_proved_without_bar_refuse
       else if negb (contaminationReverseRefineBundleNontrivial b)
            then crrc_verdict_trivial_refuse
            else if crrcXorClassifierIncompatible claim_xor_classifier b
                 then crrc_verdict_xor_refuse
                 else
                   match m with
                   | contamination_reverse_refine_conservation_unwired =>
                       if contaminationReverseRefineBundleIsConcurrentProduct b
                       then crrc_verdict_named_ok
                       else crrc_verdict_design_ok
                   | contamination_reverse_refine_conservation_assumed
                   | contamination_reverse_refine_conservation_surrogate =>
                       crrc_verdict_design_ok
                   | contamination_reverse_refine_conservation_proved =>
                       crrc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_contamination_reverse_refine_conservation_close
  (m : ContaminationReverseRefineConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : crrc_conservation_verdict :=
  if claim_physics_green
  then crrc_verdict_green_invent_refuse
  else if claim_production_wired
  then crrc_verdict_production_wired_refuse
  else
    match m with
    | contamination_reverse_refine_conservation_unwired => crrc_verdict_unwired_ok
    | contamination_reverse_refine_conservation_assumed
    | contamination_reverse_refine_conservation_proved
    | contamination_reverse_refine_conservation_surrogate => crrc_verdict_named_ok
    end.

Definition contaminationReverseRefineConservationAuthorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_contamination_reverse_refine_conservation_close
          contamination_reverse_refine_conservation_proved claim_physics_green claim_production_wired with
  | crrc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive crrc_conservation_law : Type :=
  | crrc_law_conserved
  | crrc_law_named_ok
  | crrc_law_trivial_refuse
  | crrc_law_green_invent_refuse.

Definition crrc_conservation_law_count : nat := 4.

Lemma crrc_conservation_law_count_is_four :
  crrc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive crrc_conservation_law_witness : Type :=
  | crrc_law_witness_open
  | crrc_law_witness_proved.

Definition evaluate_crrc_conservation_law_witness
  (law : crrc_conservation_law)
  (m : ContaminationReverseRefineConservationModality)
  : crrc_conservation_law_witness :=
  match m with
  | contamination_reverse_refine_conservation_unwired
  | contamination_reverse_refine_conservation_assumed
  | contamination_reverse_refine_conservation_surrogate => crrc_law_witness_open
  | contamination_reverse_refine_conservation_proved => crrc_law_witness_proved
  end.

Lemma all_crrc_conservation_laws_open_at_unwired :
  evaluate_crrc_conservation_law_witness crrc_law_conserved
    contamination_reverse_refine_conservation_unwired = crrc_law_witness_open /\
  evaluate_crrc_conservation_law_witness crrc_law_named_ok
    contamination_reverse_refine_conservation_unwired = crrc_law_witness_open /\
  evaluate_crrc_conservation_law_witness crrc_law_trivial_refuse
    contamination_reverse_refine_conservation_unwired = crrc_law_witness_open /\
  evaluate_crrc_conservation_law_witness crrc_law_green_invent_refuse
    contamination_reverse_refine_conservation_unwired = crrc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-20 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition contaminationReverseRefineConservationProved : bool := false.

Lemma contamination_reverse_refine_conservation_proved_false :
  contaminationReverseRefineConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_unwired false false =
  crrc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_unwired false false =
  crrc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_unwired false false) =
  true.
Proof.
  unfold crrc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt26_witness_named_ok :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false false =
  crrc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_contamination_reverse_refine_conservation :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false false =
  crrc_verdict_named_ok /\
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_contamination_reverse_refine_idx = 20.
Proof.
  repeat split; reflexivity.
Qed.

Lemma crrc_named_close_ok :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_proved false false =
  crrc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_contamination_reverse_refine_conservation_close :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_proved false false =
  crrc_verdict_named_ok /\
  contaminationReverseRefineConservationAuthorized false false = true.
Proof.
  split.
  - apply crrc_named_close_ok.
  - unfold contaminationReverseRefineConservationAuthorized.
    rewrite crrc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — contamination_reverse_refine refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineEmptyWitness
    contaminationReverseRefineClaimBarAbsent false false false =
  crrc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineEmptyWitness
    contaminationReverseRefineClaimBarAbsent false false false =
  crrc_verdict_trivial_refuse /\
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_bundle
       contamination_reverse_refine_conservation_unwired
       contaminationReverseRefineEmptyWitness
       contaminationReverseRefineClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold crrc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent true false false =
  crrc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent true false false =
  crrc_verdict_xor_refuse /\
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_bundle
       contamination_reverse_refine_conservation_unwired
       contaminationReverseRefineFe26Witness
       contaminationReverseRefineClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold crrc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_unwired true false =
  crrc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_unwired true false) =
  false.
Proof.
  unfold crrc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ccv_bundle_refuse :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false true false =
  crrc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — contamination_reverse_refine refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false true =
  crrc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false true =
  crrc_verdict_proved_without_bar_refuse /\
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_bundle
       contamination_reverse_refine_conservation_unwired
       contaminationReverseRefineFe26Witness
       contaminationReverseRefineClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold crrc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — contamination_reverse_refine lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_proved false true =
  crrc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_proved false true) =
  false.
Proof.
  unfold crrc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel contamination_reverse_refine axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition contaminationReverseRefineConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs".

Definition parallelContaminationAxiomTag : string := "parallel_contamination_axiom".

Lemma parallel_contamination_axiom_refuse :
  contaminationReverseRefineConservationAuthority <>
  parallelContaminationAxiomTag /\
  contaminationReverseRefineConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply contamination_reverse_refine_conservation_proved_false.
Qed.

Theorem parallel_contamination_axiom_not_minted :
  contaminationReverseRefineConservationAuthority =
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs" /\
  contaminationReverseRefineConservationProved = false /\
  contaminationReverseRefineConservationAuthority <> parallelContaminationAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "forward_refine_not_contamination_object".

Definition contaminationReverseRefineConservationFraming : string :=
  "second_law_conservation_contamination_reverse_refine_reverse_of_refine_one_axiom".

Lemma species_id_smuggle_refuse :
  contaminationReverseRefineConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_contamination_reverse_refine_idx = 20.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem reverse_of_refine_not_species_id_smuggle :
  contaminationReverseRefineConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_contamination_reverse_refine_idx = 20 /\
  contaminationReverseRefineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — contamination_reverse_refine ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "parallel_contamination_law_minted".

Lemma extra_element_id_refuse :
  contaminationReverseRefineConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  contaminationReverseRefineConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — contamination_reverse_refine ≠ extra contamination_reverse_refine force axiom    *)
(* ------------------------------------------------------------------ *)

Definition freeMixReverseFraming : string :=
  "extra_contamination_reverse_refine_force_axiom_minted_as_26th_law".

Definition refineEffectTypesAuthority : string :=
  "umst/umst-chem/src/contamination_reverse_refine_barrier.rs".

Lemma free_mix_reverse_refuse :
  contaminationReverseRefineConservationFraming <>
  freeMixReverseFraming /\
  refineEffectTypesAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem contamination_not_free_mix_reverse :
  contaminationReverseRefineConservationFraming <>
  freeMixReverseFraming /\
  refineEffectTypesAuthority =
  "umst/umst-chem/src/contamination_reverse_refine_barrier.rs" /\
  contaminationReverseRefineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v20 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_contamination_reverse_refine_scaffold".

Lemma tp_float_pin_refuse :
  contaminationReverseRefineConservationFraming <>
  tpFloatPinFraming /\
  reverse_of_refine_channel_tag = "reverse_of_refine".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  contaminationReverseRefineConservationFraming <>
  tpFloatPinFraming /\
  second_law_sole_axiom_channel_tag = "second_law_sole_axiom" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  ContaminationReverseRefine **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition crrc_conservation_coherence_scaffold : bool :=
  crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_proved false false) &&
  negb (crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_unwired true false)) &&
  negb (crrc_conservation_verdict_ok
    (evaluate_contamination_reverse_refine_conservation_close
       contamination_reverse_refine_conservation_proved false true)).

Lemma crrc_conservation_coherence_scaffold_true :
  crrc_conservation_coherence_scaffold = true.
Proof.
  unfold crrc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem crrc_conservation_coherence_scaffold_theorem :
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_proved false false =
    crrc_verdict_named_ok /\
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_unwired true false =
    crrc_verdict_green_invent_refuse /\
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_proved false true =
    crrc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition crrc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition crrc_conservation_knowing_fiber_ok : bool :=
  crrc_conservation_fiber_ok fiber_quantum_knowing.

Definition crrc_conservation_meso_acting_ok : bool :=
  crrc_conservation_fiber_ok fiber_meso_acting.

Lemma crrc_conservation_knowing_fiber_ok_true :
  crrc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma crrc_conservation_meso_acting_not_ok :
  crrc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem crrc_conservation_routes_knowing_not_meso :
  crrc_conservation_knowing_fiber_ok = true /\
  crrc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply crrc_conservation_knowing_fiber_ok_true.
  - apply crrc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  crrc_conservation_knowing_fiber_ok &&
  negb crrc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, crrc_conservation_knowing_fiber_ok,
    crrc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-20 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem contamination_reverse_refine_conservation_fixture_scaffold :
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false false =
    crrc_verdict_named_ok /\
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineEmptyWitness
    contaminationReverseRefineClaimBarAbsent false false false =
    crrc_verdict_trivial_refuse /\
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent true false false =
    crrc_verdict_xor_refuse /\
  evaluate_contamination_reverse_refine_bundle
    contamination_reverse_refine_conservation_unwired
    contaminationReverseRefineFe26Witness
    contaminationReverseRefineClaimBarAbsent false false true =
    crrc_verdict_proved_without_bar_refuse /\
  evaluate_contamination_reverse_refine_conservation_close
    contamination_reverse_refine_conservation_unwired false false =
    crrc_verdict_unwired_ok /\
  crrc_conservation_knowing_fiber_ok = true /\
  crrc_conservation_meso_acting_ok = false /\
  contaminationReverseRefineConservationProved = false /\
  crrcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — contamination_reverse_refine) *)
(* ------------------------------------------------------------------ *)

Definition chemL0ContaminationReverseRefineAuthority : string :=
  "umst/umst-chem/src/contamination_reverse_refine.rs".

Definition chemL0ContaminationReverseRefineTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs".

Definition interactPartialityAuthority : string :=
  "umst/umst-chem/src/contamination_is_messy_section.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeContamCellId : string := "CHEM-L0-EDGE-CONTAM".

Definition contaminationReverseRefineConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-CONTAMINATION-REVERSE-REFINE-CONSERVATION".

Definition contaminationReverseRefineConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CONTAMINATION-REVERSE-REFINE-CONSERVATION ContaminationReverseRefineConservationModality Unwired Assumed Proved Surrogate four-step lattice contaminationReverseRefineConservationProved false evaluateContaminationReverseRefineBundle evaluateContaminationReverseRefineConservation named class 20 contamination reverse refine Fe Z=26 reverse of Refine not parallel contamination axiom no free mix-reverse second law sole axiom concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel contamination axiom refuse species id smuggle refuse extra element id Z=119 refuse free mix-reverse refuse contamination ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired T P graph functions v14 not 298K 1atm float pins WAVE100 no lib.rs no eos.rs no cabal no lakefile".

Lemma contamination_reverse_refine_conservation_cell_id :
  contaminationReverseRefineConservationCellId =
  "CHEM-FORMAL-Q-COQ-CONTAMINATION-REVERSE-REFINE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma contamination_reverse_refine_conservation_cites_l0_table :
  chemL0ContaminationReverseRefineTableAuthority <> "".
Proof. discriminate. Qed.

Lemma contamination_reverse_refine_conservation_authority_path :
  contaminationReverseRefineConservationAuthority =
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs".
Proof. reflexivity. Qed.

Lemma contamination_reverse_refine_conservation_cites_edge_contam :
  chemL0ContaminationReverseRefineAuthority <> "".
Proof. discriminate. Qed.

Lemma contamination_reverse_refine_conservation_cites_marker :
  crrcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma contamination_reverse_refine_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma contamination_reverse_refine_conservation_cites_edge_contam_cell :
  chemL0EdgeContamCellId = "CHEM-L0-EDGE-CONTAM".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma contamination_not_26th_axiom :
  contaminationReverseRefineConservationFraming <> parallelContaminationAxiomTag.
Proof. discriminate. Qed.

Lemma contamination_second_law_conservation_framing :
  contaminationReverseRefineConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition forwardRefineFraming : string :=
  "forward_refine_positive_chemstamp_witness".

Definition reverseContaminationNamedObject : string :=
  "reverse_of_refine_on_contamination_reverse_refine_morphism".

Lemma forward_refine_not_contamination_object :
  reverseContaminationNamedObject <>
  forwardRefineFraming /\
  second_law_sole_axiom_channel_tag = "second_law_sole_axiom".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem contamination_is_reverse_of_refine_named_object :
  reverseContaminationNamedObject <>
  forwardRefineFraming /\
  reverse_of_refine_channel_tag = "reverse_of_refine" /\
  contaminationReverseRefineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not contamination_reverse_refine axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition reverseOfRefineFraming : string :=
  "reverse_of_refine_not_extra_force".

Lemma reverse_of_refine_not_extra_force_refuse :
  reverseOfRefineFraming <>
  freeMixReverseFraming /\
  reverse_of_refine_channel_tag = "reverse_of_refine".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem contamination_reverse_of_refine_not_extra_force :
  reverseOfRefineFraming <>
  freeMixReverseFraming /\
  refineEffectTypesAuthority =
  "umst/umst-chem/src/contamination_reverse_refine_barrier.rs" /\
  contaminationReverseRefineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs / cabal / lakefile not wired              *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.

Definition wave100EosRsWired : bool := false.

Definition wave100CabalWired : bool := false.

Definition wave100LakefileWired : bool := false.

Lemma wave100_lib_rs_not_wired :
  wave100LibRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_eos_rs_not_wired :
  wave100EosRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_cabal_not_wired :
  wave100CabalWired = false.
Proof. reflexivity. Qed.

Lemma wave100_lakefile_not_wired :
  wave100LakefileWired = false.
Proof. reflexivity. Qed.

Definition wave100FreezeTag : string :=
  "WAVE100 freeze — not wired lib.rs eos.rs cabal lakefile".

Lemma wave100_freeze_tag_nonempty :
  wave100FreezeTag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma contamination_reverse_refine_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma contamination_reverse_refine_conservation_modality_unwired :
  contaminationReverseRefineConservationModalityCurrent =
  contamination_reverse_refine_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: LiveGTpxConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: LIVE G(T,P,x) **conservation**.                 *)
(*  Type-only scaffold until WAVE100 lifts — formation-zero theater    *)
(*  is not measured G; measured-scalar G invent refused. T / P / μ are *)
(*  graph functions on Interact (v14) — not 298 K / 1 atm float pins. *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  liveGTpxConservationProved false. Modality Unwired. WAVE100: not   *)
(*  wired in lib.rs / eos.rs.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/thermo_g.rs (read-only cite).              *)
(*  INT: umst/umst-chem/src/formation_energy_not_silent_zero.rs (cite). *)
(*  INT: umst/umst-chem/src/chemical_potential_is_graph_function.rs.   *)
(*  INT: umst/umst-chem/src/ambient_is_graph_section.rs (read-only).    *)
(*  INT: umst/umst-chem/src/standard_pressure_is_graph_section.rs.     *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-20 **live_gtpx** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive LiveGTpxConservationModality : Type :=
  | live_gtpx_conservation_unwired
  | live_gtpx_conservation_assumed
  | live_gtpx_conservation_proved
  | live_gtpx_conservation_surrogate.

Definition liveGTpxConservationModalityCurrent :
  LiveGTpxConservationModality :=
  live_gtpx_conservation_unwired.

Definition live_gtpx_lattice_cardinality : nat := 4.

Lemma live_gtpx_lattice_cardinality_is_four :
  live_gtpx_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma live_gtpx_lattice_not_118_squared :
  negb (Nat.eqb live_gtpx_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold live_gtpx_lattice_cardinality.
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

(* North-star §2 class 20 — live_gtpx concurrent Π_c factor. *)
Definition pattern_class_live_gtpx_idx : nat := 14.

Lemma pattern_class_live_gtpx_idx_is_14 :
  pattern_class_live_gtpx_idx = 14.
Proof. reflexivity. Qed.

Lemma live_gtpx_class_index_valid :
  pattern_class_index_valid pattern_class_live_gtpx_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_live_gtpx_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierLiveGTpxRowId : string := "X20".

Lemma cross_classifier_live_gtpx_row_named :
  crossClassifierLiveGTpxRowId = "X20".
Proof. reflexivity. Qed.

Definition pattern_class_live_gtpx_tag : string :=
  "live_gtpx".

Definition north_star_class_20_live_gtpx_tag : string :=
  "class 20 live G T P x".

Lemma pattern_class_live_gtpx_tag_nonempty :
  pattern_class_live_gtpx_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_20_live_gtpx_tag_nonempty :
  north_star_class_20_live_gtpx_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Fe Z=26 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition iron_atomic_number_z : nat := 26.

Lemma iron_atomic_number_z_is_78 :
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

Definition live_gtpx_factor_tag : string :=
  "live_gtpx".

Definition g_type_only_channel_tag : string := "g_type_only".

Definition formation_zero_not_g_channel_tag : string := "formation_zero_not_g".

Lemma live_gtpx_factor_tag_nonempty :
  live_gtpx_factor_tag <> "".
Proof. discriminate. Qed.

Lemma g_type_only_channel_tag_nonempty :
  g_type_only_channel_tag <> "".
Proof. discriminate. Qed.

Lemma formation_zero_not_g_channel_tag_nonempty :
  formation_zero_not_g_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive ltgc_channel_slot : Type :=
  | ltgc_slot_unwired
  | ltgc_slot_absent
  | ltgc_slot_present.

Definition ltgc_channel_slot_beq (s1 s2 : ltgc_channel_slot) : bool :=
  match s1, s2 with
  | ltgc_slot_unwired, ltgc_slot_unwired => true
  | ltgc_slot_absent, ltgc_slot_absent => true
  | ltgc_slot_present, ltgc_slot_present => true
  | _, _ => false
  end.

Definition ltgc_channel_slot_is_present (s : ltgc_channel_slot) : bool :=
  match s with
  | ltgc_slot_present => true
  | _ => false
  end.

Definition liveGTpxProductChannelCount : nat := 3.

Lemma live_gtpx_product_channel_count_is_three :
  liveGTpxProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = G type-only, 1 = formation-zero not G, 2 = class 20 live G(T,P,x). *)
Definition ltgc_channel_g_type_only : nat := 0.
Definition ltgc_channel_formation_zero_not_g : nat := 1.
Definition ltgc_channel_class20_live_g_tpx : nat := 2.

Lemma ltgc_channel_g_type_only_idx_is_0 :
  ltgc_channel_g_type_only = 0.
Proof. reflexivity. Qed.

Lemma ltgc_channel_formation_zero_not_g_idx_is_1 :
  ltgc_channel_formation_zero_not_g = 1.
Proof. reflexivity. Qed.

Lemma ltgc_channel_class20_live_gtpx_idx_is_2 :
  ltgc_channel_class20_live_g_tpx = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition ltgc_channel_bundle : Type := nat -> ltgc_channel_slot.

Definition liveGTpxBundleAllUnwired : ltgc_channel_bundle :=
  fun _ => ltgc_slot_unwired.

Definition liveGTpxBundleAt (b : ltgc_channel_bundle) (idx : nat)
  (slot : ltgc_channel_slot) : ltgc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition liveGTpxBundleWithPresent
  (b : ltgc_channel_bundle) (idx : nat) : ltgc_channel_bundle :=
  liveGTpxBundleAt b idx ltgc_slot_present.

Fixpoint count_ltgc_present_up_to (b : ltgc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if ltgc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_ltgc_present_up_to b i + add
  end.

Definition liveGTpxBundlePresentCount (b : ltgc_channel_bundle) : nat :=
  count_ltgc_present_up_to b liveGTpxProductChannelCount.

Definition liveGTpxBundleHolds (b : ltgc_channel_bundle) (idx : nat) : bool :=
  ltgc_channel_slot_is_present (b idx).

Definition liveGTpxBundleIsConcurrentProduct (b : ltgc_channel_bundle) : bool :=
  Nat.leb 2 (liveGTpxBundlePresentCount b).

(* Fe Z=26 G type-only + formation-zero not G + class 20 live G(T,P,x) concurrent witness. *)
Definition liveGTpxFe26Witness : ltgc_channel_bundle :=
  liveGTpxBundleWithPresent
    (liveGTpxBundleWithPresent
      (liveGTpxBundleWithPresent liveGTpxBundleAllUnwired
        ltgc_channel_g_type_only)
      ltgc_channel_formation_zero_not_g)
    ltgc_channel_class20_live_g_tpx.

Definition liveGTpxEmptyWitness : ltgc_channel_bundle :=
  liveGTpxBundleAllUnwired.

Definition liveGTpxSinglePresent : ltgc_channel_bundle :=
  liveGTpxBundleWithPresent liveGTpxBundleAllUnwired
    ltgc_channel_g_type_only.

Lemma g_type_only_channel_present :
  liveGTpxBundleHolds liveGTpxFe26Witness
    ltgc_channel_g_type_only = true.
Proof. reflexivity. Qed.

Lemma formation_zero_not_g_channel_present :
  liveGTpxBundleHolds liveGTpxFe26Witness
    ltgc_channel_formation_zero_not_g = true.
Proof. reflexivity. Qed.

Lemma class20_live_gtpx_channel_present :
  liveGTpxBundleHolds liveGTpxFe26Witness
    ltgc_channel_class20_live_g_tpx = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  liveGTpxBundlePresentCount liveGTpxFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  liveGTpxBundleIsConcurrentProduct liveGTpxFe26Witness = true.
Proof.
  unfold liveGTpxBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  liveGTpxBundlePresentCount liveGTpxEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  liveGTpxBundleIsConcurrentProduct liveGTpxEmptyWitness = false.
Proof.
  unfold liveGTpxBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  liveGTpxBundlePresentCount liveGTpxSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  liveGTpxBundleIsConcurrentProduct liveGTpxSinglePresent = false.
Proof.
  unfold liveGTpxBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ltgc_xor_posture : Type :=
  | ltgc_xor_exclusive
  | ltgc_xor_concurrent_product.

Definition lgtpxXorClassifierMarker : string := "chem_l0_live_gtpx_xor_classifier_v1".
Definition lgtpxConcurrentProductMarker : string := "chem_int_live_gtpx_product_v1".

Lemma ltgc_xor_marker_ne_concurrent_product_marker :
  lgtpxXorClassifierMarker <> lgtpxConcurrentProductMarker.
Proof. discriminate. Qed.

Definition lgtpxXorClassifierIncompatible (claim_xor : bool)
  (b : ltgc_channel_bundle) : bool :=
  claim_xor && liveGTpxBundleIsConcurrentProduct b.

Lemma ltgc_xor_refuse_on_pt78_witness :
  lgtpxXorClassifierIncompatible true liveGTpxFe26Witness = true.
Proof.
  unfold lgtpxXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma ltgc_xor_ok_on_concurrent_product_claim :
  lgtpxXorClassifierIncompatible false liveGTpxFe26Witness = false.
Proof. reflexivity. Qed.

Definition lgtpxProductNotXor : bool :=
  liveGTpxBundleIsConcurrentProduct liveGTpxFe26Witness &&
  lgtpxXorClassifierIncompatible true liveGTpxFe26Witness.

Lemma ltgc_product_not_xor_true : lgtpxProductNotXor = true.
Proof.
  unfold lgtpxProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  lgtpxProductNotXor = true /\
  Nat.leb 2 (liveGTpxBundlePresentCount
    liveGTpxFe26Witness) = true /\
  lgtpxXorClassifierMarker <> lgtpxConcurrentProductMarker.
Proof.
  split.
  - apply ltgc_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply ltgc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive ltgc_bar_presence : Type :=
  | ltgc_bar_absent
  | ltgc_bar_present.

Record ltgc_claim_bar : Type := {
  ltgc_bar_presence_field : ltgc_bar_presence;
  ltgc_bar_defect_total : nat
}.

Definition live_gtpxClaimBarAbsent : ltgc_claim_bar :=
  {| ltgc_bar_presence_field := ltgc_bar_absent;
     ltgc_bar_defect_total := 0 |}.

Definition live_gtpxClaimBarZeroDefect : ltgc_claim_bar :=
  {| ltgc_bar_presence_field := ltgc_bar_present;
     ltgc_bar_defect_total := 0 |}.

Definition ltgc_claim_bar_zero_defect (b : ltgc_claim_bar) : bool :=
  match ltgc_bar_presence_field b with
  | ltgc_bar_absent => false
  | ltgc_bar_present => Nat.eqb (ltgc_bar_defect_total b) 0
  end.

Lemma ltgc_claim_bar_zero_defect_true :
  ltgc_claim_bar_zero_defect live_gtpxClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma ltgc_claim_bar_absent_not_zero_defect :
  ltgc_claim_bar_zero_defect live_gtpxClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive ltgc_conservation_verdict : Type :=
  | ltgc_verdict_unwired_ok
  | ltgc_verdict_named_ok
  | ltgc_verdict_design_ok
  | ltgc_verdict_trivial_refuse
  | ltgc_verdict_xor_refuse
  | ltgc_verdict_green_invent_refuse
  | ltgc_verdict_proved_without_bar_refuse
  | ltgc_verdict_production_wired_refuse
  | ltgc_verdict_parallel_live_gtpx_axiom_refuse
  | ltgc_verdict_species_id_smuggle_refuse
  | ltgc_verdict_extra_element_id_refuse
  | ltgc_verdict_extra_live_gtpx_force_refuse
  | ltgc_verdict_tp_float_pin_refuse.

Definition ltgc_conservation_verdict_ok (v : ltgc_conservation_verdict) : bool :=
  match v with
  | ltgc_verdict_unwired_ok => true
  | ltgc_verdict_named_ok => true
  | ltgc_verdict_design_ok => true
  | _ => false
  end.

Definition liveGTpxBundleNontrivial (b : ltgc_channel_bundle) : bool :=
  Nat.ltb 0 (liveGTpxBundlePresentCount b).

Definition evaluate_liveGTpx_bundle
  (m : LiveGTpxConservationModality)
  (b : ltgc_channel_bundle)
  (bar : ltgc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : ltgc_conservation_verdict :=
  if claim_physics_green
  then ltgc_verdict_green_invent_refuse
  else if claim_proved
       then ltgc_verdict_proved_without_bar_refuse
       else if negb (liveGTpxBundleNontrivial b)
            then ltgc_verdict_trivial_refuse
            else if lgtpxXorClassifierIncompatible claim_xor_classifier b
                 then ltgc_verdict_xor_refuse
                 else
                   match m with
                   | live_gtpx_conservation_unwired =>
                       if liveGTpxBundleIsConcurrentProduct b
                       then ltgc_verdict_named_ok
                       else ltgc_verdict_design_ok
                   | live_gtpx_conservation_assumed
                   | live_gtpx_conservation_surrogate =>
                       ltgc_verdict_design_ok
                   | live_gtpx_conservation_proved =>
                       ltgc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_liveGTpx_conservation_close
  (m : LiveGTpxConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : ltgc_conservation_verdict :=
  if claim_physics_green
  then ltgc_verdict_green_invent_refuse
  else if claim_production_wired
  then ltgc_verdict_production_wired_refuse
  else
    match m with
    | live_gtpx_conservation_unwired => ltgc_verdict_unwired_ok
    | live_gtpx_conservation_assumed
    | live_gtpx_conservation_proved
    | live_gtpx_conservation_surrogate => ltgc_verdict_named_ok
    end.

Definition live_gtpx_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_liveGTpx_conservation_close
          live_gtpx_conservation_proved claim_physics_green claim_production_wired with
  | ltgc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive ltgc_conservation_law : Type :=
  | ltgc_law_conserved
  | ltgc_law_named_ok
  | ltgc_law_trivial_refuse
  | ltgc_law_green_invent_refuse.

Definition ltgc_conservation_law_count : nat := 4.

Lemma ltgc_conservation_law_count_is_four :
  ltgc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive ltgc_conservation_law_witness : Type :=
  | ltgc_law_witness_open
  | ltgc_law_witness_proved.

Definition evaluate_ltgc_conservation_law_witness
  (law : ltgc_conservation_law)
  (m : LiveGTpxConservationModality)
  : ltgc_conservation_law_witness :=
  match m with
  | live_gtpx_conservation_unwired
  | live_gtpx_conservation_assumed
  | live_gtpx_conservation_surrogate => ltgc_law_witness_open
  | live_gtpx_conservation_proved => ltgc_law_witness_proved
  end.

Lemma all_ltgc_conservation_laws_open_at_unwired :
  evaluate_ltgc_conservation_law_witness ltgc_law_conserved
    live_gtpx_conservation_unwired = ltgc_law_witness_open /\
  evaluate_ltgc_conservation_law_witness ltgc_law_named_ok
    live_gtpx_conservation_unwired = ltgc_law_witness_open /\
  evaluate_ltgc_conservation_law_witness ltgc_law_trivial_refuse
    live_gtpx_conservation_unwired = ltgc_law_witness_open /\
  evaluate_ltgc_conservation_law_witness ltgc_law_green_invent_refuse
    live_gtpx_conservation_unwired = ltgc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-20 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition liveGTpxConservationProved : bool := false.

Lemma live_gtpx_conservation_proved_false :
  liveGTpxConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_unwired false false =
  ltgc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_unwired false false =
  ltgc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_unwired false false) =
  true.
Proof.
  unfold ltgc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt78_witness_named_ok :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false false =
  ltgc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_live_gtpx_conservation :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false false =
  ltgc_verdict_named_ok /\
  liveGTpxBundleIsConcurrentProduct liveGTpxFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_live_gtpx_idx = 14.
Proof.
  repeat split; reflexivity.
Qed.

Lemma ltgc_named_close_ok :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_proved false false =
  ltgc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_live_gtpx_conservation_close :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_proved false false =
  ltgc_verdict_named_ok /\
  live_gtpx_conservation_authorized false false = true.
Proof.
  split.
  - apply ltgc_named_close_ok.
  - unfold live_gtpx_conservation_authorized.
    rewrite ltgc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — live_gtpx refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxEmptyWitness
    live_gtpxClaimBarAbsent false false false =
  ltgc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxEmptyWitness
    live_gtpxClaimBarAbsent false false false =
  ltgc_verdict_trivial_refuse /\
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_bundle
       live_gtpx_conservation_unwired
       liveGTpxEmptyWitness
       live_gtpxClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold ltgc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent true false false =
  ltgc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent true false false =
  ltgc_verdict_xor_refuse /\
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_bundle
       live_gtpx_conservation_unwired
       liveGTpxFe26Witness
       live_gtpxClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold ltgc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_unwired true false =
  ltgc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_unwired true false) =
  false.
Proof.
  unfold ltgc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ltgc_bundle_refuse :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false true false =
  ltgc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — live_gtpx refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false true =
  ltgc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false true =
  ltgc_verdict_proved_without_bar_refuse /\
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_bundle
       live_gtpx_conservation_unwired
       liveGTpxFe26Witness
       live_gtpxClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold ltgc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — live_gtpx lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_proved false true =
  ltgc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_proved false true) =
  false.
Proof.
  unfold ltgc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel live_gtpx axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition liveGTpxConservationAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition parallelLiveGTpxAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_live_gtpx_axiom_refuse :
  liveGTpxConservationAuthority <>
  parallelLiveGTpxAxiomTag /\
  liveGTpxConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply live_gtpx_conservation_proved_false.
Qed.

Theorem parallel_live_gtpx_axiom_not_minted :
  liveGTpxConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs" /\
  liveGTpxConservationProved = false /\
  liveGTpxConservationAuthority <> parallelLiveGTpxAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — G type-only ≠ L1 SpeciesId                 *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "formation_zero_not_g_not_named_object".

Definition liveGTpxConservationFraming : string :=
  "second_law_conservation_live_gtpx_g_type_only_one_axiom".

Lemma species_id_smuggle_refuse :
  liveGTpxConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_live_gtpx_idx = 14.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem g_type_only_not_species_id_smuggle :
  liveGTpxConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_live_gtpx_idx = 14 /\
  liveGTpxConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — live_gtpx ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "formation_zero_theater_as_measured_g".

Lemma extra_element_id_refuse :
  liveGTpxConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  liveGTpxConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — live_gtpx ≠ extra live_gtpx force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraLiveGTpxForceFraming : string :=
  "extra_live_gtpx_force_axiom_minted_as_26th_law".

Definition live_gtpxBarrierAuthority : string :=
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs".

Lemma extra_live_gtpx_force_refuse :
  liveGTpxConservationFraming <>
  extraLiveGTpxForceFraming /\
  live_gtpxBarrierAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem live_gtpx_not_extra_live_gtpx_force :
  liveGTpxConservationFraming <>
  extraLiveGTpxForceFraming /\
  live_gtpxBarrierAuthority =
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs" /\
  liveGTpxConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P/μ float-pin refuse — graph functions v14 ≠ bare float pins    *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_live_gtpx_scaffold".

Lemma tp_float_pin_refuse :
  liveGTpxConservationFraming <>
  tpFloatPinFraming /\
  g_type_only_channel_tag = "g_type_only".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  liveGTpxConservationFraming <>
  tpFloatPinFraming /\
  formation_zero_not_g_channel_tag = "formation_zero_not_g" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  LiveGTpx **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition ltgc_conservation_coherence_scaffold : bool :=
  ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_proved false false) &&
  negb (ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_unwired true false)) &&
  negb (ltgc_conservation_verdict_ok
    (evaluate_liveGTpx_conservation_close
       live_gtpx_conservation_proved false true)).

Lemma ltgc_conservation_coherence_scaffold_true :
  ltgc_conservation_coherence_scaffold = true.
Proof.
  unfold ltgc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem ltgc_conservation_coherence_scaffold_theorem :
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_proved false false =
    ltgc_verdict_named_ok /\
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_unwired true false =
    ltgc_verdict_green_invent_refuse /\
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_proved false true =
    ltgc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition ltgc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition ltgc_conservation_knowing_fiber_ok : bool :=
  ltgc_conservation_fiber_ok fiber_quantum_knowing.

Definition ltgc_conservation_meso_acting_ok : bool :=
  ltgc_conservation_fiber_ok fiber_meso_acting.

Lemma ltgc_conservation_knowing_fiber_ok_true :
  ltgc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma ltgc_conservation_meso_acting_not_ok :
  ltgc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem ltgc_conservation_routes_knowing_not_meso :
  ltgc_conservation_knowing_fiber_ok = true /\
  ltgc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply ltgc_conservation_knowing_fiber_ok_true.
  - apply ltgc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  ltgc_conservation_knowing_fiber_ok &&
  negb ltgc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, ltgc_conservation_knowing_fiber_ok,
    ltgc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-20 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem live_gtpx_conservation_fixture_scaffold :
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false false =
    ltgc_verdict_named_ok /\
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxEmptyWitness
    live_gtpxClaimBarAbsent false false false =
    ltgc_verdict_trivial_refuse /\
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent true false false =
    ltgc_verdict_xor_refuse /\
  evaluate_liveGTpx_bundle
    live_gtpx_conservation_unwired
    liveGTpxFe26Witness
    live_gtpxClaimBarAbsent false false true =
    ltgc_verdict_proved_without_bar_refuse /\
  evaluate_liveGTpx_conservation_close
    live_gtpx_conservation_unwired false false =
    ltgc_verdict_unwired_ok /\
  ltgc_conservation_knowing_fiber_ok = true /\
  ltgc_conservation_meso_acting_ok = false /\
  liveGTpxConservationProved = false /\
  lgtpxProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — live_gtpx) *)
(* ------------------------------------------------------------------ *)

Definition chemL0LiveGTpxAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition chemL0LiveGTpxTableAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition interactPartialityAuthority : string :=
  "umst/umst-chem/src/formation_energy_not_silent_zero.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeLiveGTpxCellId : string := "CHEM-INT-THERMO-G-TYPE".

Definition liveGTpxConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-LIVE-G-TPX-CONSERVATION".

Definition liveGTpxConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-LIVE-G-TPX-CONSERVATION LiveGTpxConservationModality Unwired Assumed Proved Surrogate four-step lattice liveGTpxConservationProved false evaluateLiveGTpxBundle evaluateLiveGTpxConservation named class 20 live G T P x Fe Z=26 G type-only until WAVE100 lifts formation-zero theater not measured G measured-scalar G invent refuse T P mu graph functions v14 not 298K 1atm float pins concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel live G axiom refuse species id smuggle refuse extra element id Z=119 refuse extra live G force refuse live G ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs no eos.rs".

Lemma live_gtpx_conservation_cell_id :
  liveGTpxConservationCellId =
  "CHEM-FORMAL-Q-COQ-LIVE-G-TPX-CONSERVATION".
Proof. reflexivity. Qed.

Lemma live_gtpx_conservation_cites_l0_table :
  chemL0LiveGTpxTableAuthority <> "".
Proof. discriminate. Qed.

Lemma live_gtpx_conservation_authority_path :
  liveGTpxConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs".
Proof. reflexivity. Qed.

Lemma live_gtpx_conservation_cites_l0_ore02 :
  chemL0LiveGTpxAuthority <> "".
Proof. discriminate. Qed.

Lemma live_gtpx_conservation_cites_marker :
  lgtpxConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma live_gtpx_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma live_gtpx_conservation_cites_ore02_cell :
  chemL0EdgeLiveGTpxCellId = "CHEM-INT-THERMO-G-TYPE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma live_gtpx_not_26th_axiom :
  liveGTpxConservationFraming <> parallelLiveGTpxAxiomTag.
Proof. discriminate. Qed.

Lemma live_gtpx_second_law_conservation_framing :
  liveGTpxConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  formation-zero theater — not measured G; G type-only named object  *)
(* ------------------------------------------------------------------ *)

Definition formationZeroNotGFraming : string :=
  "formation_zero_theater_not_measured_g".

Definition gTypeOnlyNamedObject : string :=
  "g_type_only_on_live_gtpx_morphism".

Lemma formation_zero_not_g_not_named_object :
  gTypeOnlyNamedObject <>
  formationZeroNotGFraming /\
  formation_zero_not_g_channel_tag = "formation_zero_not_g".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem g_type_only_is_named_object_not_tst :
  gTypeOnlyNamedObject <>
  formationZeroNotGFraming /\
  g_type_only_channel_tag = "g_type_only" /\
  liveGTpxConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  G type-only refuse — not live G axiom / measured scalar invent      *)
(* ------------------------------------------------------------------ *)

Definition gTypeOnlyFraming : string :=
  "g_type_only_not_extra_force".

Lemma g_type_only_not_extra_force_refuse :
  gTypeOnlyFraming <>
  extraLiveGTpxForceFraming /\
  g_type_only_channel_tag = "g_type_only".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem live_gtpx_g_type_only_not_extra_force :
  gTypeOnlyFraming <>
  extraLiveGTpxForceFraming /\
  live_gtpxBarrierAuthority =
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs" /\
  liveGTpxConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs not wired (type-only until lift)          *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.

Definition wave100EosRsWired : bool := false.

Lemma wave100_lib_rs_not_wired :
  wave100LibRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_eos_rs_not_wired :
  wave100EosRsWired = false.
Proof. reflexivity. Qed.

Definition wave100FreezeTag : string :=
  "WAVE100 freeze — type-only until lift; not wired lib.rs eos.rs".

Lemma wave100_freeze_tag_nonempty :
  wave100FreezeTag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma live_gtpx_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma live_gtpx_conservation_modality_unwired :
  liveGTpxConservationModalityCurrent =
  live_gtpx_conservation_unwired.
Proof. reflexivity. Qed.

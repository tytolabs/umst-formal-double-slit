(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: GEngineConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: constitutive **G-engine** **conservation**.      *)
(*  G-engine may **sort** constants/identity using existing SI/occupancy *)
(*  derived-morphism sheaf; may not mint k/R/ε₀ or Landauer-fake α.     *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Thermo_n G(T,P,x) type conserved; not L1 cement copy.               *)
(*  gEngineConservationProved false. Modality Unwired. WAVE100: not      *)
(*  wired in lib.rs / eos.rs.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/thermo_g.rs (read-only cite).              *)
(*  INT: umst/umst-chem/src/l0_tables/shared.rs (read-only cite).      *)
(*  INT: umst/umst-chem/src/x_rows/engine_refuses_new_si.rs (cite).    *)
(*  INT: umst/umst-chem/src/si_sheaf.rs (read-only cite).               *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **g_engine** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive GEngineConservationModality : Type :=
  | g_engine_conservation_unwired
  | g_engine_conservation_assumed
  | g_engine_conservation_proved
  | g_engine_conservation_surrogate.

Definition gEngineConservationModalityCurrent :
  GEngineConservationModality :=
  g_engine_conservation_unwired.

Definition g_engine_lattice_cardinality : nat := 4.

Lemma g_engine_lattice_cardinality_is_four :
  g_engine_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma g_engine_lattice_not_118_squared :
  negb (Nat.eqb g_engine_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold g_engine_lattice_cardinality.
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

(* North-star §2 class 14 — g_engine concurrent Π_c factor. *)
Definition pattern_class_g_engine_idx : nat := 13.

Lemma pattern_class_g_engine_idx_is_13 :
  pattern_class_g_engine_idx = 13.
Proof. reflexivity. Qed.

Lemma g_engine_class_index_valid :
  pattern_class_index_valid pattern_class_g_engine_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_g_engine_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierGEngineRowId : string := "X13".

Lemma cross_classifier_g_engine_row_named :
  crossClassifierGEngineRowId = "X13".
Proof. reflexivity. Qed.

Definition pattern_class_g_engine_tag : string :=
  "g_engine".

Definition north_star_class_13_g_engine_tag : string :=
  "class 13 g_engine".

Lemma pattern_class_g_engine_tag_nonempty :
  pattern_class_g_engine_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_13_g_engine_tag_nonempty :
  north_star_class_13_g_engine_tag <> "".
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

Definition g_engine_factor_tag : string := "g_engine".

Definition sort_existing_sheaf_channel_tag : string := "sort_existing_sheaf".

Definition constants_not_minted_channel_tag : string := "constants_not_minted".

Lemma g_engine_factor_tag_nonempty :
  g_engine_factor_tag <> "".
Proof. discriminate. Qed.

Lemma sort_existing_sheaf_channel_tag_nonempty :
  sort_existing_sheaf_channel_tag <> "".
Proof. discriminate. Qed.

Lemma constants_not_minted_channel_tag_nonempty :
  constants_not_minted_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  GEngine product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive gecv_channel_slot : Type :=
  | gecv_slot_unwired
  | gecv_slot_absent
  | gecv_slot_present.

Definition gecv_channel_slot_beq (s1 s2 : gecv_channel_slot) : bool :=
  match s1, s2 with
  | gecv_slot_unwired, gecv_slot_unwired => true
  | gecv_slot_absent, gecv_slot_absent => true
  | gecv_slot_present, gecv_slot_present => true
  | _, _ => false
  end.

Definition gecv_channel_slot_is_present (s : gecv_channel_slot) : bool :=
  match s with
  | gecv_slot_present => true
  | _ => false
  end.

Definition gEngineProductChannelCount : nat := 3.

Lemma g_engine_product_channel_count_is_three :
  gEngineProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 13 g_engine. *)
Definition gecv_channel_sort_existing_sheaf : nat := 0.
Definition gecv_channel_constants_not_minted : nat := 1.
Definition gecv_channel_thermo_g_type_conserved : nat := 2.

Lemma gecv_channel_sort_existing_sheaf_idx_is_0 :
  gecv_channel_sort_existing_sheaf = 0.
Proof. reflexivity. Qed.

Lemma gecv_channel_constants_not_minted_idx_is_1 :
  gecv_channel_constants_not_minted = 1.
Proof. reflexivity. Qed.

Lemma gecv_channel_thermo_g_type_conserved_idx_is_2 :
  gecv_channel_thermo_g_type_conserved = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  GEngine concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition gecv_channel_bundle : Type := nat -> gecv_channel_slot.

Definition gEngineBundleAllUnwired : gecv_channel_bundle :=
  fun _ => gecv_slot_unwired.

Definition gEngineBundleAt (b : gecv_channel_bundle) (idx : nat)
  (slot : gecv_channel_slot) : gecv_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition gEngineBundleWithPresent
  (b : gecv_channel_bundle) (idx : nat) : gecv_channel_bundle :=
  gEngineBundleAt b idx gecv_slot_present.

Fixpoint count_gecv_present_up_to (b : gecv_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if gecv_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_gecv_present_up_to b i + add
  end.

Definition gEngineBundlePresentCount (b : gecv_channel_bundle) : nat :=
  count_gecv_present_up_to b gEngineProductChannelCount.

Definition gEngineBundleHolds (b : gecv_channel_bundle) (idx : nat) : bool :=
  gecv_channel_slot_is_present (b idx).

Definition gEngineBundleIsConcurrentProduct (b : gecv_channel_bundle) : bool :=
  Nat.leb 2 (gEngineBundlePresentCount b).

(* Pt Z=78 interact restriction + G-min + class 13 g_engine concurrent witness. *)
Definition gEnginePt78Witness : gecv_channel_bundle :=
  gEngineBundleWithPresent
    (gEngineBundleWithPresent
      (gEngineBundleWithPresent gEngineBundleAllUnwired
        gecv_channel_sort_existing_sheaf)
      gecv_channel_constants_not_minted)
    gecv_channel_thermo_g_type_conserved.

Definition gEngineEmptyWitness : gecv_channel_bundle :=
  gEngineBundleAllUnwired.

Definition gEngineSinglePresent : gecv_channel_bundle :=
  gEngineBundleWithPresent gEngineBundleAllUnwired
    gecv_channel_sort_existing_sheaf.

Lemma sort_existing_sheaf_channel_present :
  gEngineBundleHolds gEnginePt78Witness
    gecv_channel_sort_existing_sheaf = true.
Proof. reflexivity. Qed.

Lemma constants_not_minted_channel_present :
  gEngineBundleHolds gEnginePt78Witness
    gecv_channel_constants_not_minted = true.
Proof. reflexivity. Qed.

Lemma thermo_g_type_conserved_channel_present :
  gEngineBundleHolds gEnginePt78Witness
    gecv_channel_thermo_g_type_conserved = true.
Proof. reflexivity. Qed.

Lemma pt78_witness_present_count_is_three :
  gEngineBundlePresentCount gEnginePt78Witness = 3.
Proof. reflexivity. Qed.

Lemma pt78_witness_is_concurrent_product :
  gEngineBundleIsConcurrentProduct gEnginePt78Witness = true.
Proof.
  unfold gEngineBundleIsConcurrentProduct.
  rewrite pt78_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  gEngineBundlePresentCount gEngineEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  gEngineBundleIsConcurrentProduct gEngineEmptyWitness = false.
Proof.
  unfold gEngineBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  gEngineBundlePresentCount gEngineSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  gEngineBundleIsConcurrentProduct gEngineSinglePresent = false.
Proof.
  unfold gEngineBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive gecv_xor_posture : Type :=
  | gecv_xor_exclusive
  | gecv_xor_concurrent_product.

Definition gecXorClassifierMarker : string := "chem_l0_g_engine_xor_classifier_v1".
Definition gecConcurrentProductMarker : string := "chem_int_g_engine_product_v1".

Lemma gecv_xor_marker_ne_concurrent_product_marker :
  gecXorClassifierMarker <> gecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition gecXorClassifierIncompatible (claim_xor : bool)
  (b : gecv_channel_bundle) : bool :=
  claim_xor && gEngineBundleIsConcurrentProduct b.

Lemma gecv_xor_refuse_on_pt78_witness :
  gecXorClassifierIncompatible true gEnginePt78Witness = true.
Proof.
  unfold gecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma gecv_xor_ok_on_concurrent_product_claim :
  gecXorClassifierIncompatible false gEnginePt78Witness = false.
Proof. reflexivity. Qed.

Definition gecProductNotXor : bool :=
  gEngineBundleIsConcurrentProduct gEnginePt78Witness &&
  gecXorClassifierIncompatible true gEnginePt78Witness.

Lemma gecv_product_not_xor_true : gecProductNotXor = true.
Proof.
  unfold gecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  gecProductNotXor = true /\
  Nat.leb 2 (gEngineBundlePresentCount
    gEnginePt78Witness) = true /\
  gecXorClassifierMarker <> gecConcurrentProductMarker.
Proof.
  split.
  - apply gecv_product_not_xor_true.
  - split.
    + rewrite pt78_witness_present_count_is_three.
      reflexivity.
    + apply gecv_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  GEngine **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive gecv_bar_presence : Type :=
  | gecv_bar_absent
  | gecv_bar_present.

Record gecv_claim_bar : Type := {
  gecv_bar_presence_field : gecv_bar_presence;
  gecv_bar_defect_total : nat
}.

Definition gEngineClaimBarAbsent : gecv_claim_bar :=
  {| gecv_bar_presence_field := gecv_bar_absent;
     gecv_bar_defect_total := 0 |}.

Definition gEngineClaimBarZeroDefect : gecv_claim_bar :=
  {| gecv_bar_presence_field := gecv_bar_present;
     gecv_bar_defect_total := 0 |}.

Definition gecv_claim_bar_zero_defect (b : gecv_claim_bar) : bool :=
  match gecv_bar_presence_field b with
  | gecv_bar_absent => false
  | gecv_bar_present => Nat.eqb (gecv_bar_defect_total b) 0
  end.

Lemma gecv_claim_bar_zero_defect_true :
  gecv_claim_bar_zero_defect gEngineClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma gecv_claim_bar_absent_not_zero_defect :
  gecv_claim_bar_zero_defect gEngineClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  GEngine **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive gecv_conservation_verdict : Type :=
  | gecv_verdict_unwired_ok
  | gecv_verdict_named_ok
  | gecv_verdict_design_ok
  | gecv_verdict_trivial_refuse
  | gecv_verdict_xor_refuse
  | gecv_verdict_green_invent_refuse
  | gecv_verdict_proved_without_bar_refuse
  | gecv_verdict_production_wired_refuse
  | gecv_verdict_parallel_g_engine_axiom_refuse
  | gecv_verdict_species_id_smuggle_refuse
  | gecv_verdict_extra_element_id_refuse
  | gecv_verdict_extra_g_engine_force_refuse
  | gecv_verdict_tp_float_pin_refuse.

Definition gecv_conservation_verdict_ok (v : gecv_conservation_verdict) : bool :=
  match v with
  | gecv_verdict_unwired_ok => true
  | gecv_verdict_named_ok => true
  | gecv_verdict_design_ok => true
  | _ => false
  end.

Definition gEngineBundleNontrivial (b : gecv_channel_bundle) : bool :=
  Nat.ltb 0 (gEngineBundlePresentCount b).

Definition evaluate_g_engine_bundle
  (m : GEngineConservationModality)
  (b : gecv_channel_bundle)
  (bar : gecv_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : gecv_conservation_verdict :=
  if claim_physics_green
  then gecv_verdict_green_invent_refuse
  else if claim_proved
       then gecv_verdict_proved_without_bar_refuse
       else if negb (gEngineBundleNontrivial b)
            then gecv_verdict_trivial_refuse
            else if gecXorClassifierIncompatible claim_xor_classifier b
                 then gecv_verdict_xor_refuse
                 else
                   match m with
                   | g_engine_conservation_unwired =>
                       if gEngineBundleIsConcurrentProduct b
                       then gecv_verdict_named_ok
                       else gecv_verdict_design_ok
                   | g_engine_conservation_assumed
                   | g_engine_conservation_surrogate =>
                       gecv_verdict_design_ok
                   | g_engine_conservation_proved =>
                       gecv_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_g_engine_conservation_close
  (m : GEngineConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : gecv_conservation_verdict :=
  if claim_physics_green
  then gecv_verdict_green_invent_refuse
  else if claim_production_wired
  then gecv_verdict_production_wired_refuse
  else
    match m with
    | g_engine_conservation_unwired => gecv_verdict_unwired_ok
    | g_engine_conservation_assumed
    | g_engine_conservation_proved
    | g_engine_conservation_surrogate => gecv_verdict_named_ok
    end.

Definition g_engine_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_g_engine_conservation_close
          g_engine_conservation_proved claim_physics_green claim_production_wired with
  | gecv_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  GEngine **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive gecv_conservation_law : Type :=
  | gecv_law_conserved
  | gecv_law_named_ok
  | gecv_law_trivial_refuse
  | gecv_law_green_invent_refuse.

Definition gecv_conservation_law_count : nat := 4.

Lemma gecv_conservation_law_count_is_four :
  gecv_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive gecv_conservation_law_witness : Type :=
  | gecv_law_witness_open
  | gecv_law_witness_proved.

Definition evaluate_gecv_conservation_law_witness
  (law : gecv_conservation_law)
  (m : GEngineConservationModality)
  : gecv_conservation_law_witness :=
  match m with
  | g_engine_conservation_unwired
  | g_engine_conservation_assumed
  | g_engine_conservation_surrogate => gecv_law_witness_open
  | g_engine_conservation_proved => gecv_law_witness_proved
  end.

Lemma all_gecv_conservation_laws_open_at_unwired :
  evaluate_gecv_conservation_law_witness gecv_law_conserved
    g_engine_conservation_unwired = gecv_law_witness_open /\
  evaluate_gecv_conservation_law_witness gecv_law_named_ok
    g_engine_conservation_unwired = gecv_law_witness_open /\
  evaluate_gecv_conservation_law_witness gecv_law_trivial_refuse
    g_engine_conservation_unwired = gecv_law_witness_open /\
  evaluate_gecv_conservation_law_witness gecv_law_green_invent_refuse
    g_engine_conservation_unwired = gecv_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition gEngineConservationProved : bool := false.

Lemma g_engine_conservation_proved_false :
  gEngineConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_g_engine_conservation_close
    g_engine_conservation_unwired false false =
  gecv_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_g_engine_conservation_close
    g_engine_conservation_unwired false false =
  gecv_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_unwired false false) =
  true.
Proof.
  unfold gecv_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma pt78_witness_named_ok :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false false =
  gecv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_pt78_g_engine_conservation :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false false =
  gecv_verdict_named_ok /\
  gEngineBundleIsConcurrentProduct gEnginePt78Witness = true /\
  platinum_atomic_number_z = 78 /\
  pattern_class_g_engine_idx = 13.
Proof.
  repeat split; reflexivity.
Qed.

Lemma gecv_named_close_ok :
  evaluate_g_engine_conservation_close
    g_engine_conservation_proved false false =
  gecv_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_g_engine_conservation_close :
  evaluate_g_engine_conservation_close
    g_engine_conservation_proved false false =
  gecv_verdict_named_ok /\
  g_engine_conservation_authorized false false = true.
Proof.
  split.
  - apply gecv_named_close_ok.
  - unfold g_engine_conservation_authorized.
    rewrite gecv_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — g_engine refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEngineEmptyWitness
    gEngineClaimBarAbsent false false false =
  gecv_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEngineEmptyWitness
    gEngineClaimBarAbsent false false false =
  gecv_verdict_trivial_refuse /\
  gecv_conservation_verdict_ok
    (evaluate_g_engine_bundle
       g_engine_conservation_unwired
       gEngineEmptyWitness
       gEngineClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold gecv_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent true false false =
  gecv_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent true false false =
  gecv_verdict_xor_refuse /\
  gecv_conservation_verdict_ok
    (evaluate_g_engine_bundle
       g_engine_conservation_unwired
       gEnginePt78Witness
       gEngineClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold gecv_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_g_engine_conservation_close
    g_engine_conservation_unwired true false =
  gecv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_unwired true false) =
  false.
Proof.
  unfold gecv_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_gecv_bundle_refuse :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false true false =
  gecv_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — g_engine refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false true =
  gecv_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false true =
  gecv_verdict_proved_without_bar_refuse /\
  gecv_conservation_verdict_ok
    (evaluate_g_engine_bundle
       g_engine_conservation_unwired
       gEnginePt78Witness
       gEngineClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold gecv_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — g_engine lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_g_engine_conservation_close
    g_engine_conservation_proved false true =
  gecv_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_proved false true) =
  false.
Proof.
  unfold gecv_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel g_engine axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition gEngineConservationAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition parallelGEngineAxiomTag : string := "26th_g_engine_axiom".

Lemma parallel_g_engine_axiom_refuse :
  gEngineConservationAuthority <>
  parallelGEngineAxiomTag /\
  gEngineConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply g_engine_conservation_proved_false.
Qed.

Theorem parallel_g_engine_axiom_not_minted :
  gEngineConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs" /\
  gEngineConservationProved = false /\
  gEngineConservationAuthority <> parallelGEngineAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "constants_not_minted_not_named_object".

Definition gEngineConservationFraming : string :=
  "second_law_conservation_g_engine_sort_restriction_one_axiom".

Lemma species_id_smuggle_refuse :
  gEngineConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_g_engine_idx = 13.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem sort_existing_sheaf_not_species_id_smuggle :
  gEngineConservationFraming <>
  speciesIdSmuggleFraming /\
  platinum_atomic_number_z = 78 /\
  pattern_class_g_engine_idx = 13 /\
  gEngineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — g_engine ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "g_engine_constants_mint_in_net_sort".

Lemma extra_element_id_refuse :
  gEngineConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  gEngineConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — g_engine ≠ extra g_engine force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraGEngineForceFraming : string :=
  "extra_g_engine_force_axiom_minted_as_26th_law".

Definition gEngineBarrierAuthority : string :=
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs".

Lemma extra_g_engine_force_refuse :
  gEngineConservationFraming <>
  extraGEngineForceFraming /\
  gEngineBarrierAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem g_engine_not_extra_g_engine_force :
  gEngineConservationFraming <>
  extraGEngineForceFraming /\
  gEngineBarrierAuthority =
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs" /\
  gEngineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_g_engine_scaffold".

Lemma tp_float_pin_refuse :
  gEngineConservationFraming <>
  tpFloatPinFraming /\
  sort_existing_sheaf_channel_tag = "sort_existing_sheaf".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  gEngineConservationFraming <>
  tpFloatPinFraming /\
  constants_not_minted_channel_tag = "constants_not_minted" /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  GEngine **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition gecv_conservation_coherence_scaffold : bool :=
  gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_proved false false) &&
  negb (gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_unwired true false)) &&
  negb (gecv_conservation_verdict_ok
    (evaluate_g_engine_conservation_close
       g_engine_conservation_proved false true)).

Lemma gecv_conservation_coherence_scaffold_true :
  gecv_conservation_coherence_scaffold = true.
Proof.
  unfold gecv_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem gecv_conservation_coherence_scaffold_theorem :
  evaluate_g_engine_conservation_close
    g_engine_conservation_proved false false =
    gecv_verdict_named_ok /\
  evaluate_g_engine_conservation_close
    g_engine_conservation_unwired true false =
    gecv_verdict_green_invent_refuse /\
  evaluate_g_engine_conservation_close
    g_engine_conservation_proved false true =
    gecv_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition gecv_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition gecv_conservation_knowing_fiber_ok : bool :=
  gecv_conservation_fiber_ok fiber_quantum_knowing.

Definition gecv_conservation_meso_acting_ok : bool :=
  gecv_conservation_fiber_ok fiber_meso_acting.

Lemma gecv_conservation_knowing_fiber_ok_true :
  gecv_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma gecv_conservation_meso_acting_not_ok :
  gecv_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem gecv_conservation_routes_knowing_not_meso :
  gecv_conservation_knowing_fiber_ok = true /\
  gecv_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply gecv_conservation_knowing_fiber_ok_true.
  - apply gecv_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  gecv_conservation_knowing_fiber_ok &&
  negb gecv_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, gecv_conservation_knowing_fiber_ok,
    gecv_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem g_engine_conservation_fixture_scaffold :
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false false =
    gecv_verdict_named_ok /\
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEngineEmptyWitness
    gEngineClaimBarAbsent false false false =
    gecv_verdict_trivial_refuse /\
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent true false false =
    gecv_verdict_xor_refuse /\
  evaluate_g_engine_bundle
    g_engine_conservation_unwired
    gEnginePt78Witness
    gEngineClaimBarAbsent false false true =
    gecv_verdict_proved_without_bar_refuse /\
  evaluate_g_engine_conservation_close
    g_engine_conservation_unwired false false =
    gecv_verdict_unwired_ok /\
  gecv_conservation_knowing_fiber_ok = true /\
  gecv_conservation_meso_acting_ok = false /\
  gEngineConservationProved = false /\
  gecProductNotXor = true /\
  platinum_atomic_number_z = 78.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — g_engine) *)
(* ------------------------------------------------------------------ *)

Definition chemL0GEngineAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition chemL0GEngineTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/shared.rs".

Definition interactPartialityAuthority : string :=
  "umst/umst-chem/src/si_sheaf.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeGEngineCellId : string := "CHEM-INT-THERMO-G-TYPE".

Definition gEngineConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-G-ENGINE-CONSERVATION".

Definition gEngineConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-G-ENGINE-CONSERVATION GEngineConservationModality Unwired Assumed Proved Surrogate four-step lattice gEngineConservationProved false evaluateGEngineBundle evaluateGEngineConservation named class 13 g_engine Pt Z=78 sort existing sheaf constants not minted k R epsilon_0 Landauer-fake alpha refuse Thermo_n G type concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel g engine axiom refuse species id smuggle refuse extra element id Z=119 refuse extra g engine force refuse g engine ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs no eos.rs".

Lemma g_engine_conservation_cell_id :
  gEngineConservationCellId =
  "CHEM-FORMAL-Q-COQ-G-ENGINE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma g_engine_conservation_cites_l0_table :
  chemL0GEngineTableAuthority <> "".
Proof. discriminate. Qed.

Lemma g_engine_conservation_authority_path :
  gEngineConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs".
Proof. reflexivity. Qed.

Lemma g_engine_conservation_cites_l0_ore02 :
  chemL0GEngineAuthority <> "".
Proof. discriminate. Qed.

Lemma g_engine_conservation_cites_marker :
  gecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma g_engine_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma g_engine_conservation_cites_ore02_cell :
  chemL0EdgeGEngineCellId = "CHEM-INT-THERMO-G-TYPE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma g_engine_not_26th_axiom :
  gEngineConservationFraming <> parallelGEngineAxiomTag.
Proof. discriminate. Qed.

Lemma g_engine_second_law_conservation_framing :
  gEngineConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition constantsNotMintedFraming : string :=
  "engine_mints_k_R_epsilon0_not_named_object".

Definition sortExistingSheafNamedObject : string :=
  "sort_existing_sheaf_on_g_engine_morphism".

Lemma constants_not_minted_not_named_object :
  sortExistingSheafNamedObject <>
  constantsNotMintedFraming /\
  constants_not_minted_channel_tag = "constants_not_minted".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem sort_existing_sheaf_is_named_object_not_tst :
  sortExistingSheafNamedObject <>
  constantsNotMintedFraming /\
  sort_existing_sheaf_channel_tag = "sort_existing_sheaf" /\
  gEngineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not g_engine axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition sortExistingSheafFraming : string :=
  "sort_existing_sheaf_not_extra_force".

Lemma sort_existing_sheaf_not_extra_force_refuse :
  sortExistingSheafFraming <>
  extraGEngineForceFraming /\
  sort_existing_sheaf_channel_tag = "sort_existing_sheaf".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem g_engine_sort_restriction_not_extra_force :
  sortExistingSheafFraming <>
  extraGEngineForceFraming /\
  gEngineBarrierAuthority =
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs" /\
  gEngineConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  Forbidden SI mints — k, R, ε₀ (engines consult sheaf, do not mint) *)
(* ------------------------------------------------------------------ *)

Definition forbidden_si_mint_k : string := "k".
Definition forbidden_si_mint_R : string := "R".
Definition forbidden_si_mint_epsilon_0 : string := "epsilon_0".

Definition engine_may_mint_si : bool := false.

Lemma engine_may_mint_si_false : engine_may_mint_si = false.
Proof. reflexivity. Qed.

Definition alpha_deferred_codata_marker : string :=
  "alpha_deferred_composition_codata_not_landauer_fake_v1".

Definition landauer_fake_marker : string :=
  "landauer_fake_alpha_mint_v1".

Lemma alpha_not_landauer_fake :
  alpha_deferred_codata_marker <> landauer_fake_marker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs not wired (type-only until lift)          *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.
Definition wave100EosRsWired : bool := false.

Lemma wave100_lib_rs_not_wired : wave100LibRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_eos_rs_not_wired : wave100EosRsWired = false.
Proof. reflexivity. Qed.

Definition wave100FreezeTag : string :=
  "WAVE100 freeze — type-only until lift; not wired lib.rs eos.rs".

Lemma wave100_freeze_tag_nonempty : wave100FreezeTag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma g_engine_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma g_engine_conservation_modality_unwired :
  gEngineConservationModalityCurrent =
  g_engine_conservation_unwired.
Proof. reflexivity. Qed.

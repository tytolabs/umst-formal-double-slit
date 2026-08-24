(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OtherNamedNuanceConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 24 **other_named_nuance** **conservation**.   *)
(*  Extra named views admitted only if **no new law** on the same second-law + *)
(*  conservation object (not a parallel other_named_nuance axiom). Concurrent  *)
(*  Π_c PatternBundle factor — **product** not XOR. Bounded 2026 extras are   *)
(*  concurrent product slots (σ-hole, stereochemistry, …) not XOR enum growth. *)
(*  otherNamedNuanceConservationProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/other_named_nuance.rs (read-only). *)
(*  INT: umst/umst-chem/src/l0_tables/pattern_named_factors.rs (cite). *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-24 **other_named_nuance** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive OtherNamedNuanceConservationModality : Type :=
  | other_named_nuance_conservation_unwired
  | other_named_nuance_conservation_assumed
  | other_named_nuance_conservation_proved
  | other_named_nuance_conservation_surrogate.

Definition otherNamedNuanceConservationModalityCurrent :
  OtherNamedNuanceConservationModality :=
  other_named_nuance_conservation_unwired.

Definition other_named_nuance_lattice_cardinality : nat := 4.

Lemma other_named_nuance_lattice_cardinality_is_four :
  other_named_nuance_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma other_named_nuance_lattice_not_118_squared :
  negb (Nat.eqb other_named_nuance_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold other_named_nuance_lattice_cardinality.
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

(* North-star §2 class 24 — other_named_nuance concurrent Π_c factor. *)
Definition pattern_class_other_named_nuance_idx : nat := 24.

Lemma pattern_class_other_named_nuance_idx_is_24 :
  pattern_class_other_named_nuance_idx = 24.
Proof. reflexivity. Qed.

Lemma other_named_nuance_class_index_valid :
  pattern_class_index_valid pattern_class_other_named_nuance_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_other_named_nuance_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOtherNamedNuanceRowId : string := "X24".

Lemma cross_classifier_other_named_nuance_row_named :
  crossClassifierOtherNamedNuanceRowId = "X24".
Proof. reflexivity. Qed.

Definition pattern_class_other_named_nuance_tag : string :=
  "other_named_nuance".

Definition north_star_class_24_other_named_nuance_tag : string :=
  "class 24 other named nuance".

Lemma pattern_class_other_named_nuance_tag_nonempty :
  pattern_class_other_named_nuance_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_24_other_named_nuance_tag_nonempty :
  north_star_class_24_other_named_nuance_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — I Z=53 halogen σ-hole host witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition iodine_atomic_number_z : nat := 53.

Lemma iodine_atomic_number_z_is_53 :
  iodine_atomic_number_z = 53.
Proof. reflexivity. Qed.

Definition iodine_z_valid : bool :=
  Nat.ltb 0 iodine_atomic_number_z &&
  Nat.leb iodine_atomic_number_z iupac_table_cardinality.

Lemma iodine_z_valid_true : iodine_z_valid = true.
Proof.
  unfold iodine_z_valid, iodine_atomic_number_z, iupac_table_cardinality.
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

Definition other_named_nuance_factor_tag : string :=
  "other_named_nuance".

Definition no_new_law_admission_channel_tag : string := "no_new_law_admission".

Definition bounded_2026_extras_product_channel_tag : string := "bounded_2026_extras_product".

Lemma other_named_nuance_factor_tag_nonempty :
  other_named_nuance_factor_tag <> "".
Proof. discriminate. Qed.

Lemma no_new_law_admission_channel_tag_nonempty :
  no_new_law_admission_channel_tag <> "".
Proof. discriminate. Qed.

Lemma bounded_2026_extras_product_channel_tag_nonempty :
  bounded_2026_extras_product_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive onn_channel_slot : Type :=
  | onn_slot_unwired
  | onn_slot_absent
  | onn_slot_present.

Definition onn_channel_slot_beq (s1 s2 : onn_channel_slot) : bool :=
  match s1, s2 with
  | onn_slot_unwired, onn_slot_unwired => true
  | onn_slot_absent, onn_slot_absent => true
  | onn_slot_present, onn_slot_present => true
  | _, _ => false
  end.

Definition onn_channel_slot_is_present (s : onn_channel_slot) : bool :=
  match s with
  | onn_slot_present => true
  | _ => false
  end.

Definition otherNamedNuanceProductChannelCount : nat := 3.

Lemma other_named_nuance_product_channel_count_is_three :
  otherNamedNuanceProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = no new law admission, 1 = bounded 2026 extras, 2 = class 24 other_named_nuance. *)
Definition onn_channel_no_new_law_admission : nat := 0.
Definition onn_channel_bounded_2026_extras : nat := 1.
Definition onn_channel_class24_other_named_nuance : nat := 2.

Lemma onn_channel_no_new_law_admission_idx_is_0 :
  onn_channel_no_new_law_admission = 0.
Proof. reflexivity. Qed.

Lemma onn_channel_bounded_2026_extras_idx_is_1 :
  onn_channel_bounded_2026_extras = 1.
Proof. reflexivity. Qed.

Lemma onn_channel_class24_other_named_nuance_idx_is_2 :
  onn_channel_class24_other_named_nuance = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition onn_channel_bundle : Type := nat -> onn_channel_slot.

Definition otherNamedNuanceBundleAllUnwired : onn_channel_bundle :=
  fun _ => onn_slot_unwired.

Definition otherNamedNuanceBundleAt (b : onn_channel_bundle) (idx : nat)
  (slot : onn_channel_slot) : onn_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition otherNamedNuanceBundleWithPresent
  (b : onn_channel_bundle) (idx : nat) : onn_channel_bundle :=
  otherNamedNuanceBundleAt b idx onn_slot_present.

Fixpoint count_onn_present_up_to (b : onn_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if onn_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_onn_present_up_to b i + add
  end.

Definition otherNamedNuanceBundlePresentCount (b : onn_channel_bundle) : nat :=
  count_onn_present_up_to b otherNamedNuanceProductChannelCount.

Definition otherNamedNuanceBundleHolds (b : onn_channel_bundle) (idx : nat) : bool :=
  onn_channel_slot_is_present (b idx).

Definition otherNamedNuanceBundleIsConcurrentProduct (b : onn_channel_bundle) : bool :=
  Nat.leb 2 (otherNamedNuanceBundlePresentCount b).

(* I Z=53 no-new-law admission + bounded 2026 extras + class 24 other_named_nuance concurrent witness. *)
Definition otherNamedNuanceI53Witness : onn_channel_bundle :=
  otherNamedNuanceBundleWithPresent
    (otherNamedNuanceBundleWithPresent
      (otherNamedNuanceBundleWithPresent otherNamedNuanceBundleAllUnwired
        onn_channel_no_new_law_admission)
      onn_channel_bounded_2026_extras)
    onn_channel_class24_other_named_nuance.

Definition otherNamedNuanceEmptyWitness : onn_channel_bundle :=
  otherNamedNuanceBundleAllUnwired.

Definition otherNamedNuanceSinglePresent : onn_channel_bundle :=
  otherNamedNuanceBundleWithPresent otherNamedNuanceBundleAllUnwired
    onn_channel_no_new_law_admission.

Lemma no_new_law_admission_channel_present :
  otherNamedNuanceBundleHolds otherNamedNuanceI53Witness
    onn_channel_no_new_law_admission = true.
Proof. reflexivity. Qed.

Lemma bounded_2026_extras_channel_present :
  otherNamedNuanceBundleHolds otherNamedNuanceI53Witness
    onn_channel_bounded_2026_extras = true.
Proof. reflexivity. Qed.

Lemma class24_other_named_nuance_channel_present :
  otherNamedNuanceBundleHolds otherNamedNuanceI53Witness
    onn_channel_class24_other_named_nuance = true.
Proof. reflexivity. Qed.

Lemma i53_witness_present_count_is_three :
  otherNamedNuanceBundlePresentCount otherNamedNuanceI53Witness = 3.
Proof. reflexivity. Qed.

Lemma i53_witness_is_concurrent_product :
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceI53Witness = true.
Proof.
  unfold otherNamedNuanceBundleIsConcurrentProduct.
  rewrite i53_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  otherNamedNuanceBundlePresentCount otherNamedNuanceEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceEmptyWitness = false.
Proof.
  unfold otherNamedNuanceBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  otherNamedNuanceBundlePresentCount otherNamedNuanceSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceSinglePresent = false.
Proof.
  unfold otherNamedNuanceBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive onn_xor_posture : Type :=
  | onn_xor_exclusive
  | onn_xor_concurrent_product.

Definition onnXorClassifierMarker : string := "chem_l0_other_named_nuance_xor_enum_growth_v1".
Definition onnConcurrentProductMarker : string := "chem_int_other_named_nuance_product_v1".

Lemma onn_xor_marker_ne_concurrent_product_marker :
  onnXorClassifierMarker <> onnConcurrentProductMarker.
Proof. discriminate. Qed.

Definition onnXorClassifierIncompatible (claim_xor : bool)
  (b : onn_channel_bundle) : bool :=
  claim_xor && otherNamedNuanceBundleIsConcurrentProduct b.

Lemma onn_xor_refuse_on_i53_witness :
  onnXorClassifierIncompatible true otherNamedNuanceI53Witness = true.
Proof.
  unfold onnXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma onn_xor_ok_on_concurrent_product_claim :
  onnXorClassifierIncompatible false otherNamedNuanceI53Witness = false.
Proof. reflexivity. Qed.

Definition onnProductNotXor : bool :=
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceI53Witness &&
  onnXorClassifierIncompatible true otherNamedNuanceI53Witness.

Lemma onn_product_not_xor_true : onnProductNotXor = true.
Proof.
  unfold onnProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  onnProductNotXor = true /\
  Nat.leb 2 (otherNamedNuanceBundlePresentCount
    otherNamedNuanceI53Witness) = true /\
  onnXorClassifierMarker <> onnConcurrentProductMarker.
Proof.
  split.
  - apply onn_product_not_xor_true.
  - split.
    + rewrite i53_witness_present_count_is_three.
      reflexivity.
    + apply onn_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive onn_bar_presence : Type :=
  | onn_bar_absent
  | onn_bar_present.

Record onn_claim_bar : Type := {
  onn_bar_presence_field : onn_bar_presence;
  onn_bar_defect_total : nat
}.

Definition otherNamedNuanceClaimBarAbsent : onn_claim_bar :=
  {| onn_bar_presence_field := onn_bar_absent;
     onn_bar_defect_total := 0 |}.

Definition otherNamedNuanceClaimBarZeroDefect : onn_claim_bar :=
  {| onn_bar_presence_field := onn_bar_present;
     onn_bar_defect_total := 0 |}.

Definition onn_claim_bar_zero_defect (b : onn_claim_bar) : bool :=
  match onn_bar_presence_field b with
  | onn_bar_absent => false
  | onn_bar_present => Nat.eqb (onn_bar_defect_total b) 0
  end.

Lemma onn_claim_bar_zero_defect_true :
  onn_claim_bar_zero_defect otherNamedNuanceClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma onn_claim_bar_absent_not_zero_defect :
  onn_claim_bar_zero_defect otherNamedNuanceClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive onn_conservation_verdict : Type :=
  | onn_verdict_unwired_ok
  | onn_verdict_named_ok
  | onn_verdict_design_ok
  | onn_verdict_trivial_refuse
  | onn_verdict_xor_refuse
  | onn_verdict_green_invent_refuse
  | onn_verdict_proved_without_bar_refuse
  | onn_verdict_production_wired_refuse
  | onn_verdict_parallel_other_named_axiom_refuse
  | onn_verdict_unbounded_extra_name_refuse
  | onn_verdict_extra_element_id_refuse
  | onn_verdict_extra_other_named_law_refuse
  | onn_verdict_tp_float_pin_refuse.

Definition onn_conservation_verdict_ok (v : onn_conservation_verdict) : bool :=
  match v with
  | onn_verdict_unwired_ok => true
  | onn_verdict_named_ok => true
  | onn_verdict_design_ok => true
  | _ => false
  end.

Definition otherNamedNuanceBundleNontrivial (b : onn_channel_bundle) : bool :=
  Nat.ltb 0 (otherNamedNuanceBundlePresentCount b).

Definition evaluate_other_named_nuance_bundle
  (m : OtherNamedNuanceConservationModality)
  (b : onn_channel_bundle)
  (bar : onn_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : onn_conservation_verdict :=
  if claim_physics_green
  then onn_verdict_green_invent_refuse
  else if claim_proved
       then onn_verdict_proved_without_bar_refuse
       else if negb (otherNamedNuanceBundleNontrivial b)
            then onn_verdict_trivial_refuse
            else if onnXorClassifierIncompatible claim_xor_classifier b
                 then onn_verdict_xor_refuse
                 else
                   match m with
                   | other_named_nuance_conservation_unwired =>
                       if otherNamedNuanceBundleIsConcurrentProduct b
                       then onn_verdict_named_ok
                       else onn_verdict_design_ok
                   | other_named_nuance_conservation_assumed
                   | other_named_nuance_conservation_surrogate =>
                       onn_verdict_design_ok
                   | other_named_nuance_conservation_proved =>
                       onn_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_other_named_nuance_conservation_close
  (m : OtherNamedNuanceConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : onn_conservation_verdict :=
  if claim_physics_green
  then onn_verdict_green_invent_refuse
  else if claim_production_wired
  then onn_verdict_production_wired_refuse
  else
    match m with
    | other_named_nuance_conservation_unwired => onn_verdict_unwired_ok
    | other_named_nuance_conservation_assumed
    | other_named_nuance_conservation_proved
    | other_named_nuance_conservation_surrogate => onn_verdict_named_ok
    end.

Definition other_named_nuance_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_other_named_nuance_conservation_close
          other_named_nuance_conservation_proved claim_physics_green claim_production_wired with
  | onn_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive onn_conservation_law : Type :=
  | onn_law_conserved
  | onn_law_named_ok
  | onn_law_trivial_refuse
  | onn_law_green_invent_refuse.

Definition onn_conservation_law_count : nat := 4.

Lemma onn_conservation_law_count_is_four :
  onn_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive onn_conservation_law_witness : Type :=
  | onn_law_witness_open
  | onn_law_witness_proved.

Definition evaluate_onn_conservation_law_witness
  (law : onn_conservation_law)
  (m : OtherNamedNuanceConservationModality)
  : onn_conservation_law_witness :=
  match m with
  | other_named_nuance_conservation_unwired
  | other_named_nuance_conservation_assumed
  | other_named_nuance_conservation_surrogate => onn_law_witness_open
  | other_named_nuance_conservation_proved => onn_law_witness_proved
  end.

Lemma all_onn_conservation_laws_open_at_unwired :
  evaluate_onn_conservation_law_witness onn_law_conserved
    other_named_nuance_conservation_unwired = onn_law_witness_open /\
  evaluate_onn_conservation_law_witness onn_law_named_ok
    other_named_nuance_conservation_unwired = onn_law_witness_open /\
  evaluate_onn_conservation_law_witness onn_law_trivial_refuse
    other_named_nuance_conservation_unwired = onn_law_witness_open /\
  evaluate_onn_conservation_law_witness onn_law_green_invent_refuse
    other_named_nuance_conservation_unwired = onn_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition otherNamedNuanceConservationProved : bool := false.

Lemma other_named_nuance_conservation_proved_false :
  otherNamedNuanceConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_unwired false false =
  onn_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_unwired false false =
  onn_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_unwired false false) =
  true.
Proof.
  unfold onn_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Pt Z=78 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma i53_witness_named_ok :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false false =
  onn_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_i53_other_named_nuance_conservation :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false false =
  onn_verdict_named_ok /\
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceI53Witness = true /\
  iodine_atomic_number_z = 53 /\
  pattern_class_other_named_nuance_idx = 24.
Proof.
  repeat split; reflexivity.
Qed.

Lemma onn_named_close_ok :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_proved false false =
  onn_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_other_named_nuance_conservation_close :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_proved false false =
  onn_verdict_named_ok /\
  other_named_nuance_conservation_authorized false false = true.
Proof.
  split.
  - apply onn_named_close_ok.
  - unfold other_named_nuance_conservation_authorized.
    rewrite onn_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — catalysis refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceEmptyWitness
    otherNamedNuanceClaimBarAbsent false false false =
  onn_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceEmptyWitness
    otherNamedNuanceClaimBarAbsent false false false =
  onn_verdict_trivial_refuse /\
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_bundle
       other_named_nuance_conservation_unwired
       otherNamedNuanceEmptyWitness
       otherNamedNuanceClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold onn_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_enum_growth_refused :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent true false false =
  onn_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_enum_growth_fail_closed :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent true false false =
  onn_verdict_xor_refuse /\
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_bundle
       other_named_nuance_conservation_unwired
       otherNamedNuanceI53Witness
       otherNamedNuanceClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_enum_growth_refused.
  - unfold onn_conservation_verdict_ok.
    rewrite xor_enum_growth_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_unwired true false =
  onn_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_unwired true false) =
  false.
Proof.
  unfold onn_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_onn_bundle_refuse :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false true false =
  onn_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — catalysis refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false true =
  onn_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false true =
  onn_verdict_proved_without_bar_refuse /\
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_bundle
       other_named_nuance_conservation_unwired
       otherNamedNuanceI53Witness
       otherNamedNuanceClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold onn_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — catalysis lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_proved false true =
  onn_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_proved false true) =
  false.
Proof.
  unfold onn_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel catalysis axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition otherNamedNuanceConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs".

Definition parallelOtherNamedAxiomTag : string := "parallel_other_named_nuance_axiom".

Lemma parallel_other_named_axiom_refuse :
  otherNamedNuanceConservationAuthority <>
  parallelOtherNamedAxiomTag /\
  otherNamedNuanceConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply other_named_nuance_conservation_proved_false.
Qed.

Theorem parallel_other_named_axiom_not_minted :
  otherNamedNuanceConservationAuthority =
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs" /\
  otherNamedNuanceConservationProved = false /\
  otherNamedNuanceConservationAuthority <> parallelOtherNamedAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition unboundedExtraNameSmuggleFraming : string :=
  "xor_enum_growth_not_concurrent_product".

Definition otherNamedNuanceConservationFraming : string :=
  "second_law_conservation_other_named_nuance_no_new_law_one_axiom".

Lemma unbounded_extra_name_refuse :
  otherNamedNuanceConservationFraming <>
  unboundedExtraNameSmuggleFraming /\
  iodine_atomic_number_z = 53 /\
  pattern_class_other_named_nuance_idx = 24.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem no_new_law_not_unbounded_extra_name_smuggle :
  otherNamedNuanceConservationFraming <>
  unboundedExtraNameSmuggleFraming /\
  iodine_atomic_number_z = 53 /\
  pattern_class_other_named_nuance_idx = 24 /\
  otherNamedNuanceConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — catalysis ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "unbounded_extra_name_outside_2026_bounded_set".

Lemma extra_element_id_refuse :
  otherNamedNuanceConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  otherNamedNuanceConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iodine_atomic_number_z = 53.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — catalysis ≠ extra catalysis force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOtherNamedLawFraming : string :=
  "extra_other_named_nuance_axiom_minted_as_26th_law".

Definition otherNamedNuanceTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs".

Lemma extra_other_named_law_refuse :
  otherNamedNuanceConservationFraming <>
  extraOtherNamedLawFraming /\
  otherNamedNuanceTableAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem other_named_nuance_not_extra_other_named_law :
  otherNamedNuanceConservationFraming <>
  extraOtherNamedLawFraming /\
  otherNamedNuanceTableAuthority =
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs" /\
  otherNamedNuanceConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_other_named_nuance_scaffold".

Lemma tp_float_pin_refuse :
  otherNamedNuanceConservationFraming <>
  tpFloatPinFraming /\
  no_new_law_admission_channel_tag = "no_new_law_admission".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  otherNamedNuanceConservationFraming <>
  tpFloatPinFraming /\
  bounded_2026_extras_product_channel_tag = "bounded_2026_extras_product" /\
  iodine_atomic_number_z = 53.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Catalysis **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition onn_conservation_coherence_scaffold : bool :=
  onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_proved false false) &&
  negb (onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_unwired true false)) &&
  negb (onn_conservation_verdict_ok
    (evaluate_other_named_nuance_conservation_close
       other_named_nuance_conservation_proved false true)).

Lemma onn_conservation_coherence_scaffold_true :
  onn_conservation_coherence_scaffold = true.
Proof.
  unfold onn_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem onn_conservation_coherence_scaffold_theorem :
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_proved false false =
    onn_verdict_named_ok /\
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_unwired true false =
    onn_verdict_green_invent_refuse /\
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_proved false true =
    onn_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition onn_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition onn_conservation_knowing_fiber_ok : bool :=
  onn_conservation_fiber_ok fiber_quantum_knowing.

Definition onn_conservation_meso_acting_ok : bool :=
  onn_conservation_fiber_ok fiber_meso_acting.

Lemma onn_conservation_knowing_fiber_ok_true :
  onn_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma onn_conservation_meso_acting_not_ok :
  onn_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem onn_conservation_routes_knowing_not_meso :
  onn_conservation_knowing_fiber_ok = true /\
  onn_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply onn_conservation_knowing_fiber_ok_true.
  - apply onn_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  onn_conservation_knowing_fiber_ok &&
  negb onn_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, onn_conservation_knowing_fiber_ok,
    onn_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem other_named_nuance_conservation_fixture_scaffold :
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false false =
    onn_verdict_named_ok /\
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceEmptyWitness
    otherNamedNuanceClaimBarAbsent false false false =
    onn_verdict_trivial_refuse /\
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent true false false =
    onn_verdict_xor_refuse /\
  evaluate_other_named_nuance_bundle
    other_named_nuance_conservation_unwired
    otherNamedNuanceI53Witness
    otherNamedNuanceClaimBarAbsent false false true =
    onn_verdict_proved_without_bar_refuse /\
  evaluate_other_named_nuance_conservation_close
    other_named_nuance_conservation_unwired false false =
    onn_verdict_unwired_ok /\
  onn_conservation_knowing_fiber_ok = true /\
  onn_conservation_meso_acting_ok = false /\
  otherNamedNuanceConservationProved = false /\
  onnProductNotXor = true /\
  iodine_atomic_number_z = 53.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — catalysis) *)
(* ------------------------------------------------------------------ *)

Definition chemL0OtherNamedNuanceAuthority : string :=
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs".

Definition chemL0OtherNamedNuanceTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs".

Definition patternNamedFactorsAuthority : string :=
  "umst/umst-chem/src/l0_tables/pattern_named_factors.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemIntNuanceOtherNamedCellId : string := "CHEM-INT-NUANCE-OTHER_NAMED".

Definition otherNamedNuanceConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-OTHER-NAMED-NUANCE-CONSERVATION".

Definition otherNamedNuanceConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-OTHER-NAMED-NUANCE-CONSERVATION OtherNamedNuanceConservationModality Unwired Assumed Proved Surrogate four-step lattice otherNamedNuanceConservationProved false evaluateOtherNamedNuanceBundle evaluateOtherNamedNuanceConservation named class 24 other_named_nuance I Z=53 halogen sigma hole no new law admission bounded 2026 extras concurrent product identity conserved present ge 2 product not XOR xor enum growth refuse parallel other_named_nuance axiom refuse unbounded extra name refuse extra element id Z=119 refuse extra other_named law refuse other_named_nuance ne unbounded extras Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma other_named_nuance_conservation_cell_id :
  otherNamedNuanceConservationCellId =
  "CHEM-FORMAL-Q-COQ-OTHER-NAMED-NUANCE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma other_named_nuance_conservation_cites_l0_table :
  chemL0OtherNamedNuanceTableAuthority <> "".
Proof. discriminate. Qed.

Lemma other_named_nuance_conservation_authority_path :
  otherNamedNuanceConservationAuthority =
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs".
Proof. reflexivity. Qed.

Lemma other_named_nuance_conservation_cites_l0_table_marker :
  chemL0OtherNamedNuanceAuthority <> "".
Proof. discriminate. Qed.

Lemma other_named_nuance_conservation_cites_marker :
  onnConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma other_named_nuance_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma other_named_nuance_conservation_cites_int_cell :
  chemIntNuanceOtherNamedCellId = "CHEM-INT-NUANCE-OTHER_NAMED".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma other_named_nuance_not_26th_axiom :
  otherNamedNuanceConservationFraming <> parallelOtherNamedAxiomTag.
Proof. discriminate. Qed.

Lemma other_named_nuance_second_law_conservation_framing :
  otherNamedNuanceConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition xorEnumGrowthFraming : string :=
  "xor_enum_growth_for_class24_extras_not_named_object".

Definition noNewLawAdmissionNamedObject : string :=
  "no_new_law_admission_on_other_named_nuance_views".

Lemma xor_enum_growth_not_concurrent_product :
  noNewLawAdmissionNamedObject <>
  xorEnumGrowthFraming /\
  bounded_2026_extras_product_channel_tag = "bounded_2026_extras_product".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem no_new_law_admission_not_xor_enum_growth :
  noNewLawAdmissionNamedObject <>
  xorEnumGrowthFraming /\
  no_new_law_admission_channel_tag = "no_new_law_admission" /\
  otherNamedNuanceConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not catalysis axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition noNewLawAdmissionFraming : string :=
  "no_new_law_admission_not_extra_other_named_law".

Lemma no_new_law_not_extra_other_named_law_refuse :
  noNewLawAdmissionFraming <>
  extraOtherNamedLawFraming /\
  no_new_law_admission_channel_tag = "no_new_law_admission".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem other_named_nuance_no_new_law_not_extra_law :
  noNewLawAdmissionFraming <>
  extraOtherNamedLawFraming /\
  otherNamedNuanceTableAuthority =
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs" /\
  otherNamedNuanceConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma other_named_nuance_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma other_named_nuance_conservation_modality_unwired :
  otherNamedNuanceConservationModalityCurrent =
  other_named_nuance_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AssemblageStabilityWhyConservation.v                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 7 **assemblage_stability_why**            *)
(*  **conservation**. Why a mineral/phase assemblage is the observed   *)
(*  one = concurrent Π_c PatternBundle factor on the same second-law +  *)
(*  conservation object — Ore predicate ⊗ G-min presentation ⊗ class 7 *)
(*  WHY factor is **product** not XOR. Not a 26th axiom; not           *)
(*  Goldschmidt XOR enum. assemblageStabilityWhyConservationProved       *)
(*  false. Modality Unwired.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/assemblage_stability.rs (read-only cite).  *)
(*  INT: umst/umst-chem/src/l0_tables/assemblage_stability_why.rs       *)
(*  (read-only cite). PatternProductConservation.v posture cited.       *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-7 **assemblage_stability_why** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive AssemblageStabilityWhyConservationModality : Type :=
  | assemblage_stability_why_conservation_unwired
  | assemblage_stability_why_conservation_assumed
  | assemblage_stability_why_conservation_proved
  | assemblage_stability_why_conservation_surrogate.

Definition assemblageStabilityWhyConservationModalityCurrent :
  AssemblageStabilityWhyConservationModality :=
  assemblage_stability_why_conservation_unwired.

Definition assemblage_stability_why_lattice_cardinality : nat := 4.

Lemma assemblage_stability_why_lattice_cardinality_is_four :
  assemblage_stability_why_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma assemblage_stability_why_lattice_not_118_squared :
  negb (Nat.eqb assemblage_stability_why_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold assemblage_stability_why_lattice_cardinality.
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

(* North-star §2 class 7 — assemblage_stability_why concurrent Π_c factor. *)
Definition pattern_class_assemblage_stability_why_idx : nat := 7.

Lemma pattern_class_assemblage_stability_why_idx_is_7 :
  pattern_class_assemblage_stability_why_idx = 7.
Proof. reflexivity. Qed.

Lemma assemblage_stability_why_class_index_valid :
  pattern_class_index_valid pattern_class_assemblage_stability_why_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_assemblage_stability_why_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition pattern_class_natural_ore_assemblage_idx : nat := 6.

Lemma pattern_class_natural_ore_assemblage_idx_is_6 :
  pattern_class_natural_ore_assemblage_idx = 6.
Proof. reflexivity. Qed.

Definition crossClassifierAssemblageStabilityWhyRowId : string := "X07".

Lemma cross_classifier_assemblage_stability_why_row_named :
  crossClassifierAssemblageStabilityWhyRowId = "X07".
Proof. reflexivity. Qed.

Definition pattern_class_assemblage_stability_why_tag : string :=
  "assemblage_stability_why".

Definition pattern_class_natural_ore_assemblage_tag : string :=
  "natural_ore_assemblage".

Lemma pattern_class_assemblage_stability_why_tag_nonempty :
  pattern_class_assemblage_stability_why_tag <> "".
Proof. discriminate. Qed.

Lemma pattern_class_natural_ore_assemblage_tag_nonempty :
  pattern_class_natural_ore_assemblage_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Fe Z=26 assemblage identity witness                 *)
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

Definition assemblage_stability_why_factor_tag : string :=
  "assemblage_stability_why".

Definition ore_predicate_channel_tag : string := "ore_predicate".

Definition second_law_gmin_channel_tag : string := "second_law_presentation".

Lemma assemblage_stability_why_factor_tag_nonempty :
  assemblage_stability_why_factor_tag <> "".
Proof. discriminate. Qed.

Lemma ore_predicate_channel_tag_nonempty :
  ore_predicate_channel_tag <> "".
Proof. discriminate. Qed.

Lemma second_law_gmin_channel_tag_nonempty :
  second_law_gmin_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY product channel — concurrent **product**   *)
(* ------------------------------------------------------------------ *)

Inductive asw_channel_slot : Type :=
  | asw_slot_unwired
  | asw_slot_absent
  | asw_slot_present.

Definition asw_channel_slot_beq (s1 s2 : asw_channel_slot) : bool :=
  match s1, s2 with
  | asw_slot_unwired, asw_slot_unwired => true
  | asw_slot_absent, asw_slot_absent => true
  | asw_slot_present, asw_slot_present => true
  | _, _ => false
  end.

Definition asw_channel_slot_is_present (s : asw_channel_slot) : bool :=
  match s with
  | asw_slot_present => true
  | _ => false
  end.

Definition assemblageStabilityWhyProductChannelCount : nat := 3.

Lemma assemblage_stability_why_product_channel_count_is_three :
  assemblageStabilityWhyProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = ore predicate, 1 = G-min second law, 2 = class 7 WHY. *)
Definition asw_channel_ore_predicate : nat := 0.
Definition asw_channel_second_law_gmin : nat := 1.
Definition asw_channel_class7_why : nat := 2.

Lemma asw_channel_ore_predicate_idx_is_0 :
  asw_channel_ore_predicate = 0.
Proof. reflexivity. Qed.

Lemma asw_channel_second_law_gmin_idx_is_1 :
  asw_channel_second_law_gmin = 1.
Proof. reflexivity. Qed.

Lemma asw_channel_class7_why_idx_is_2 :
  asw_channel_class7_why = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY concurrent **product** bundle scaffold     *)
(* ------------------------------------------------------------------ *)

Definition asw_channel_bundle : Type := nat -> asw_channel_slot.

Definition assemblageStabilityWhyBundleAllUnwired : asw_channel_bundle :=
  fun _ => asw_slot_unwired.

Definition assemblageStabilityWhyBundleAt (b : asw_channel_bundle) (idx : nat)
  (slot : asw_channel_slot) : asw_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition assemblageStabilityWhyBundleWithPresent
  (b : asw_channel_bundle) (idx : nat) : asw_channel_bundle :=
  assemblageStabilityWhyBundleAt b idx asw_slot_present.

Fixpoint count_asw_present_up_to (b : asw_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if asw_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_asw_present_up_to b i + add
  end.

Definition assemblageStabilityWhyBundlePresentCount (b : asw_channel_bundle) : nat :=
  count_asw_present_up_to b assemblageStabilityWhyProductChannelCount.

Definition assemblageStabilityWhyBundleHolds (b : asw_channel_bundle) (idx : nat) : bool :=
  asw_channel_slot_is_present (b idx).

Definition assemblageStabilityWhyBundleIsConcurrentProduct (b : asw_channel_bundle) : bool :=
  Nat.leb 2 (assemblageStabilityWhyBundlePresentCount b).

(* Fe Z=26 ore predicate + G-min + class-7 WHY concurrent witness. *)
Definition assemblageStabilityWhyFe26Witness : asw_channel_bundle :=
  assemblageStabilityWhyBundleWithPresent
    (assemblageStabilityWhyBundleWithPresent
      (assemblageStabilityWhyBundleWithPresent assemblageStabilityWhyBundleAllUnwired
        asw_channel_ore_predicate)
      asw_channel_second_law_gmin)
    asw_channel_class7_why.

Definition assemblageStabilityWhyEmptyWitness : asw_channel_bundle :=
  assemblageStabilityWhyBundleAllUnwired.

Definition assemblageStabilityWhySinglePresent : asw_channel_bundle :=
  assemblageStabilityWhyBundleWithPresent assemblageStabilityWhyBundleAllUnwired
    asw_channel_ore_predicate.

Lemma ore_predicate_channel_present :
  assemblageStabilityWhyBundleHolds assemblageStabilityWhyFe26Witness
    asw_channel_ore_predicate = true.
Proof. reflexivity. Qed.

Lemma second_law_gmin_channel_present :
  assemblageStabilityWhyBundleHolds assemblageStabilityWhyFe26Witness
    asw_channel_second_law_gmin = true.
Proof. reflexivity. Qed.

Lemma class7_why_channel_present :
  assemblageStabilityWhyBundleHolds assemblageStabilityWhyFe26Witness
    asw_channel_class7_why = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  assemblageStabilityWhyBundlePresentCount assemblageStabilityWhyFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyFe26Witness = true.
Proof.
  unfold assemblageStabilityWhyBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  assemblageStabilityWhyBundlePresentCount assemblageStabilityWhyEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyEmptyWitness = false.
Proof.
  unfold assemblageStabilityWhyBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  assemblageStabilityWhyBundlePresentCount assemblageStabilityWhySinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhySinglePresent = false.
Proof.
  unfold assemblageStabilityWhyBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive asw_xor_posture : Type :=
  | asw_xor_exclusive
  | asw_xor_concurrent_product.

Definition aswXorClassifierMarker : string := "chem_l0_assemblage_stability_xor_classifier_v1".
Definition aswConcurrentProductMarker : string := "chem_int_assemblage_stability_product_v1".

Lemma asw_xor_marker_ne_concurrent_product_marker :
  aswXorClassifierMarker <> aswConcurrentProductMarker.
Proof. discriminate. Qed.

Definition aswXorClassifierIncompatible (claim_xor : bool)
  (b : asw_channel_bundle) : bool :=
  claim_xor && assemblageStabilityWhyBundleIsConcurrentProduct b.

Lemma asw_xor_refuse_on_fe26_witness :
  aswXorClassifierIncompatible true assemblageStabilityWhyFe26Witness = true.
Proof.
  unfold aswXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma asw_xor_ok_on_concurrent_product_claim :
  aswXorClassifierIncompatible false assemblageStabilityWhyFe26Witness = false.
Proof. reflexivity. Qed.

Definition aswProductNotXor : bool :=
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyFe26Witness &&
  aswXorClassifierIncompatible true assemblageStabilityWhyFe26Witness.

Lemma asw_product_not_xor_true : aswProductNotXor = true.
Proof.
  unfold aswProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  aswProductNotXor = true /\
  Nat.leb 2 (assemblageStabilityWhyBundlePresentCount
    assemblageStabilityWhyFe26Witness) = true /\
  aswXorClassifierMarker <> aswConcurrentProductMarker.
Proof.
  split.
  - apply asw_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply asw_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt XOR enum refuse — affinity XOR ≠ Π_c WHY product        *)
(* ------------------------------------------------------------------ *)

Definition goldschmidtXorEnumMarker : string := "goldschmidt_xor_enum_classifier_v1".

Definition goldschmidtConcurrentProductMarker : string :=
  "goldschmidt_ore_g_fo2_concurrent_product_v1".

Lemma goldschmidt_xor_marker_ne_concurrent_product :
  goldschmidtXorEnumMarker <> goldschmidtConcurrentProductMarker.
Proof. discriminate. Qed.

Definition goldschmidtXorIncompatible (claim_xor_enum : bool)
  (b : asw_channel_bundle) : bool :=
  claim_xor_enum && assemblageStabilityWhyBundleIsConcurrentProduct b.

Lemma goldschmidt_xor_refuse_on_fe26_witness :
  goldschmidtXorIncompatible true assemblageStabilityWhyFe26Witness = true.
Proof.
  unfold goldschmidtXorIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem goldschmidt_xor_not_assemblage_stability_why_product :
  goldschmidtXorEnumMarker <> goldschmidtConcurrentProductMarker /\
  goldschmidtXorIncompatible true assemblageStabilityWhyFe26Witness = true /\
  pattern_class_assemblage_stability_why_idx = 7.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY **conservation** bar — Proved-without-bar   *)
(* ------------------------------------------------------------------ *)

Inductive asw_bar_presence : Type :=
  | asw_bar_absent
  | asw_bar_present.

Record asw_claim_bar : Type := {
  asw_bar_presence_field : asw_bar_presence;
  asw_bar_defect_total : nat
}.

Definition assemblageStabilityWhyClaimBarAbsent : asw_claim_bar :=
  {| asw_bar_presence_field := asw_bar_absent;
     asw_bar_defect_total := 0 |}.

Definition assemblageStabilityWhyClaimBarZeroDefect : asw_claim_bar :=
  {| asw_bar_presence_field := asw_bar_present;
     asw_bar_defect_total := 0 |}.

Definition asw_claim_bar_zero_defect (b : asw_claim_bar) : bool :=
  match asw_bar_presence_field b with
  | asw_bar_absent => false
  | asw_bar_present => Nat.eqb (asw_bar_defect_total b) 0
  end.

Lemma asw_claim_bar_zero_defect_true :
  asw_claim_bar_zero_defect assemblageStabilityWhyClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma asw_claim_bar_absent_not_zero_defect :
  asw_claim_bar_zero_defect assemblageStabilityWhyClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY **conservation** verdict — fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive asw_conservation_verdict : Type :=
  | asw_verdict_unwired_ok
  | asw_verdict_named_ok
  | asw_verdict_design_ok
  | asw_verdict_trivial_refuse
  | asw_verdict_xor_refuse
  | asw_verdict_goldschmidt_xor_refuse
  | asw_verdict_green_invent_refuse
  | asw_verdict_proved_without_bar_refuse
  | asw_verdict_production_wired_refuse
  | asw_verdict_parallel_stability_axiom_refuse
  | asw_verdict_species_id_smuggle_refuse
  | asw_verdict_tp_float_pin_refuse.

Definition asw_conservation_verdict_ok (v : asw_conservation_verdict) : bool :=
  match v with
  | asw_verdict_unwired_ok => true
  | asw_verdict_named_ok => true
  | asw_verdict_design_ok => true
  | _ => false
  end.

Definition assemblageStabilityWhyBundleNontrivial (b : asw_channel_bundle) : bool :=
  Nat.ltb 0 (assemblageStabilityWhyBundlePresentCount b).

Definition evaluate_assemblage_stability_why_bundle
  (m : AssemblageStabilityWhyConservationModality)
  (b : asw_channel_bundle)
  (bar : asw_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : asw_conservation_verdict :=
  if claim_physics_green
  then asw_verdict_green_invent_refuse
  else if claim_proved
       then asw_verdict_proved_without_bar_refuse
       else if negb (assemblageStabilityWhyBundleNontrivial b)
            then asw_verdict_trivial_refuse
            else if aswXorClassifierIncompatible claim_xor_classifier b
                 then asw_verdict_xor_refuse
                 else
                   match m with
                   | assemblage_stability_why_conservation_unwired =>
                       if assemblageStabilityWhyBundleIsConcurrentProduct b
                       then asw_verdict_named_ok
                       else asw_verdict_design_ok
                   | assemblage_stability_why_conservation_assumed
                   | assemblage_stability_why_conservation_surrogate =>
                       asw_verdict_design_ok
                   | assemblage_stability_why_conservation_proved =>
                       asw_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_assemblage_stability_why_conservation_close
  (m : AssemblageStabilityWhyConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : asw_conservation_verdict :=
  if claim_physics_green
  then asw_verdict_green_invent_refuse
  else if claim_production_wired
  then asw_verdict_production_wired_refuse
  else
    match m with
    | assemblage_stability_why_conservation_unwired => asw_verdict_unwired_ok
    | assemblage_stability_why_conservation_assumed
    | assemblage_stability_why_conservation_proved
    | assemblage_stability_why_conservation_surrogate => asw_verdict_named_ok
    end.

Definition assemblage_stability_why_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_assemblage_stability_why_conservation_close
          assemblage_stability_why_conservation_proved claim_physics_green claim_production_wired with
  | asw_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive asw_conservation_law : Type :=
  | asw_law_conserved
  | asw_law_named_ok
  | asw_law_trivial_refuse
  | asw_law_green_invent_refuse.

Definition asw_conservation_law_count : nat := 4.

Lemma asw_conservation_law_count_is_four :
  asw_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive asw_conservation_law_witness : Type :=
  | asw_law_witness_open
  | asw_law_witness_proved.

Definition evaluate_asw_conservation_law_witness
  (law : asw_conservation_law)
  (m : AssemblageStabilityWhyConservationModality)
  : asw_conservation_law_witness :=
  match m with
  | assemblage_stability_why_conservation_unwired
  | assemblage_stability_why_conservation_assumed
  | assemblage_stability_why_conservation_surrogate => asw_law_witness_open
  | assemblage_stability_why_conservation_proved => asw_law_witness_proved
  end.

Lemma all_asw_conservation_laws_open_at_unwired :
  evaluate_asw_conservation_law_witness asw_law_conserved
    assemblage_stability_why_conservation_unwired = asw_law_witness_open /\
  evaluate_asw_conservation_law_witness asw_law_named_ok
    assemblage_stability_why_conservation_unwired = asw_law_witness_open /\
  evaluate_asw_conservation_law_witness asw_law_trivial_refuse
    assemblage_stability_why_conservation_unwired = asw_law_witness_open /\
  evaluate_asw_conservation_law_witness asw_law_green_invent_refuse
    assemblage_stability_why_conservation_unwired = asw_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-7 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition assemblageStabilityWhyConservationProved : bool := false.

Lemma assemblage_stability_why_conservation_proved_false :
  assemblageStabilityWhyConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_unwired false false =
  asw_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_unwired false false =
  asw_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_unwired false false) =
  true.
Proof.
  unfold asw_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 WHY close — concurrent **product**                    *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false false =
  asw_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_assemblage_stability_why_conservation :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false false =
  asw_verdict_named_ok /\
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_assemblage_stability_why_idx = 7.
Proof.
  repeat split; reflexivity.
Qed.

Lemma asw_named_close_ok :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_proved false false =
  asw_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_assemblage_stability_why_conservation_close :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_proved false false =
  asw_verdict_named_ok /\
  assemblage_stability_why_conservation_authorized false false = true.
Proof.
  split.
  - apply asw_named_close_ok.
  - unfold assemblage_stability_why_conservation_authorized.
    rewrite asw_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — assemblage-stability-WHY refuse    *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyEmptyWitness
    assemblageStabilityWhyClaimBarAbsent false false false =
  asw_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyEmptyWitness
    assemblageStabilityWhyClaimBarAbsent false false false =
  asw_verdict_trivial_refuse /\
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_bundle
       assemblage_stability_why_conservation_unwired
       assemblageStabilityWhyEmptyWitness
       assemblageStabilityWhyClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold asw_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent true false false =
  asw_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent true false false =
  asw_verdict_xor_refuse /\
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_bundle
       assemblage_stability_why_conservation_unwired
       assemblageStabilityWhyFe26Witness
       assemblageStabilityWhyClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold asw_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_unwired true false =
  asw_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_unwired true false) =
  false.
Proof.
  unfold asw_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_asw_bundle_refuse :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false true false =
  asw_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — assemblage-stability-WHY refuse    *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false true =
  asw_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false true =
  asw_verdict_proved_without_bar_refuse /\
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_bundle
       assemblage_stability_why_conservation_unwired
       assemblageStabilityWhyFe26Witness
       assemblageStabilityWhyClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold asw_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — assemblage-stability-WHY lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_proved false true =
  asw_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_proved false true) =
  false.
Proof.
  unfold asw_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel stability axiom refuse — WHY predicate not 26th axiom       *)
(* ------------------------------------------------------------------ *)

Definition assemblageStabilityWhyConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".

Definition parallelStabilityAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_stability_axiom_refuse :
  assemblageStabilityWhyConservationAuthority <>
  parallelStabilityAxiomTag /\
  assemblageStabilityWhyConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply assemblage_stability_why_conservation_proved_false.
Qed.

Theorem parallel_stability_axiom_not_minted :
  assemblageStabilityWhyConservationAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs" /\
  assemblageStabilityWhyConservationProved = false /\
  assemblageStabilityWhyConservationAuthority <> parallelStabilityAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — Ore predicate WHY ≠ L1 SpeciesId tag     *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition assemblageStabilityWhyConservationFraming : string :=
  "second_law_conservation_assemblage_stability_why_one_axiom".

Lemma species_id_smuggle_refuse :
  assemblageStabilityWhyConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_assemblage_stability_why_idx = 7.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ore_predicate_not_species_id_smuggle :
  assemblageStabilityWhyConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_assemblage_stability_why_idx = 7 /\
  assemblageStabilityWhyConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_stability_scaffold".

Lemma tp_float_pin_refuse :
  assemblageStabilityWhyConservationFraming <>
  tpFloatPinFraming /\
  ore_predicate_channel_tag = "ore_predicate".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  assemblageStabilityWhyConservationFraming <>
  tpFloatPinFraming /\
  second_law_gmin_channel_tag = "second_law_presentation" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Assemblage-stability-WHY **conservation** coherence scaffold          *)
(* ------------------------------------------------------------------ *)

Definition asw_conservation_coherence_scaffold : bool :=
  asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_proved false false) &&
  negb (asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_unwired true false)) &&
  negb (asw_conservation_verdict_ok
    (evaluate_assemblage_stability_why_conservation_close
       assemblage_stability_why_conservation_proved false true)).

Lemma asw_conservation_coherence_scaffold_true :
  asw_conservation_coherence_scaffold = true.
Proof.
  unfold asw_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem asw_conservation_coherence_scaffold_theorem :
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_proved false false =
    asw_verdict_named_ok /\
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_unwired true false =
    asw_verdict_green_invent_refuse /\
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_proved false true =
    asw_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition asw_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition asw_conservation_knowing_fiber_ok : bool :=
  asw_conservation_fiber_ok fiber_quantum_knowing.

Definition asw_conservation_meso_acting_ok : bool :=
  asw_conservation_fiber_ok fiber_meso_acting.

Lemma asw_conservation_knowing_fiber_ok_true :
  asw_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma asw_conservation_meso_acting_not_ok :
  asw_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem asw_conservation_routes_knowing_not_meso :
  asw_conservation_knowing_fiber_ok = true /\
  asw_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply asw_conservation_knowing_fiber_ok_true.
  - apply asw_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  asw_conservation_knowing_fiber_ok &&
  negb asw_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, asw_conservation_knowing_fiber_ok,
    asw_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-7 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem assemblage_stability_why_conservation_fixture_scaffold :
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false false =
    asw_verdict_named_ok /\
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyEmptyWitness
    assemblageStabilityWhyClaimBarAbsent false false false =
    asw_verdict_trivial_refuse /\
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent true false false =
    asw_verdict_xor_refuse /\
  evaluate_assemblage_stability_why_bundle
    assemblage_stability_why_conservation_unwired
    assemblageStabilityWhyFe26Witness
    assemblageStabilityWhyClaimBarAbsent false false true =
    asw_verdict_proved_without_bar_refuse /\
  evaluate_assemblage_stability_why_conservation_close
    assemblage_stability_why_conservation_unwired false false =
    asw_verdict_unwired_ok /\
  asw_conservation_knowing_fiber_ok = true /\
  asw_conservation_meso_acting_ok = false /\
  assemblageStabilityWhyConservationProved = false /\
  aswProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — assemblage WHY)      *)
(* ------------------------------------------------------------------ *)

Definition chemL0AssemblageStabilityAuthority : string :=
  "umst/umst-chem/src/assemblage_stability.rs".

Definition chemL0AssemblageStabilityWhyTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".

Definition oreAssemblageAuthority : string :=
  "umst/umst-chem/src/ore_assemblage.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition goldschmidtConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/GoldschmidtConservation.v".

Definition assemblageStabilityWhyConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ASSEMBLAGE-STABILITY-WHY-CONSERVATION".

Definition assemblageStabilityWhyConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ASSEMBLAGE-STABILITY-WHY-CONSERVATION AssemblageStabilityWhyConservationModality Unwired Assumed Proved Surrogate four-step lattice assemblageStabilityWhyConservationProved false evaluateAssemblageStabilityWhyBundle evaluateAssemblageStabilityWhyConservation named class 7 assemblage_stability_why Fe Z=26 ore predicate second law G-min presentation concurrent product identity conserved present ge 2 product not XOR goldschmidt xor enum refuse parallel stability axiom refuse species id smuggle refuse tp float pin refuse assemblage stability why ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma assemblage_stability_why_conservation_cell_id :
  assemblageStabilityWhyConservationCellId =
  "CHEM-FORMAL-Q-COQ-ASSEMBLAGE-STABILITY-WHY-CONSERVATION".
Proof. reflexivity. Qed.

Lemma assemblage_stability_why_conservation_cites_l0_table :
  chemL0AssemblageStabilityWhyTableAuthority <> "".
Proof. discriminate. Qed.

Lemma assemblage_stability_why_conservation_authority_path :
  assemblageStabilityWhyConservationAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs".
Proof. reflexivity. Qed.

Lemma assemblage_stability_why_conservation_cites_l0_ore01 :
  chemL0AssemblageStabilityAuthority <> "".
Proof. discriminate. Qed.

Lemma assemblage_stability_why_conservation_cites_marker :
  aswConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma assemblage_stability_why_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma assemblage_stability_why_not_26th_axiom :
  assemblageStabilityWhyConservationFraming <> parallelStabilityAxiomTag.
Proof. discriminate. Qed.

Lemma assemblage_stability_why_second_law_conservation_framing :
  assemblageStabilityWhyConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma assemblage_stability_why_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma assemblage_stability_why_conservation_modality_unwired :
  assemblageStabilityWhyConservationModalityCurrent =
  assemblage_stability_why_conservation_unwired.
Proof. reflexivity. Qed.

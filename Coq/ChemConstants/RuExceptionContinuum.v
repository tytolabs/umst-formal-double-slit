(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: RuExceptionContinuum.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: Ru Z=44 4d⁴5s¹ **exception continuum**.          *)
(*  D-block Madelung occupancy exception as occupancy-engine sort on    *)
(*  the same second-law + conservation object (ore ⊗ isotope ⊗ purify  *)
(*  ⊗ G-stability ⊗ Env concurrent product — not XOR enum).            *)
(*  Not a 26th periodic-table axiom; homolog ≠ occupancy copy (Ta Z=73  *)
(*  same group, distinct observed override). ruExceptionContinuumProved  *)
(*  false. Modality Unwired. WAVE100 not wired lib.rs / eos.rs.         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs (read-only). *)
(*  INT: umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs (cite). *)
(*  INT: umst/umst-chem/src/x_rows/madelung_witness.rs (read-only cite). *)
(*  DBlockOccupancyExceptions.v pins cited read-only.                     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum modality (Unwired / Assumed / Proved /       *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive RuExceptionContinuumModality : Type :=
  | ru_exception_continuum_unwired
  | ru_exception_continuum_assumed
  | ru_exception_continuum_proved
  | ru_exception_continuum_surrogate.

Definition ruExceptionContinuumModalityCurrent : RuExceptionContinuumModality :=
  ru_exception_continuum_unwired.

Definition ru_exception_continuum_lattice_cardinality : nat := 4.

Lemma ru_exception_continuum_lattice_cardinality_is_four :
  ru_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma ru_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb ru_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold ru_exception_continuum_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  X29 occupancy-engine sort row pin (cite OccupancyEngineSort read-only) *)
(* ------------------------------------------------------------------ *)

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_occupancy_engine_sort_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition occupancyEngineSortBucketTag : string := "dblock_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Ru Z=44 d-block exception witness                   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition ruthenium_atomic_number_z : nat := 44.

Lemma ruthenium_atomic_number_z_is_44 :
  ruthenium_atomic_number_z = 44.
Proof. reflexivity. Qed.

Definition iron_homolog_z : nat := 26.

Lemma iron_homolog_z_is_26 :
  iron_homolog_z = 26.
Proof. reflexivity. Qed.

Definition osmium_homolog_z : nat := 76.

Lemma osmium_homolog_z_is_76 :
  osmium_homolog_z = 76.
Proof. reflexivity. Qed.

Definition ruthenium_z_valid : bool :=
  Nat.ltb 0 ruthenium_atomic_number_z &&
  Nat.leb ruthenium_atomic_number_z iupac_table_cardinality.

Lemma ruthenium_z_valid_true : ruthenium_z_valid = true.
Proof.
  unfold ruthenium_z_valid, ruthenium_atomic_number_z, iupac_table_cardinality.
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

(* ------------------------------------------------------------------ *)
(*  Ru Z=44 occupancy pins — 4d⁴5s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition ru_element_symbol : string := "Ru".

Definition ru_observed_occupancy_tag : string := "4d75s1".

Definition ru_predicted_occupancy_tag : string := "4d65s2".

Definition ru_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s14d7".

Definition ru_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d6".

Definition fe_homolog_observed_occupancy_tag : string := "3d64s2".

Definition os_homolog_observed_occupancy_tag : string := "4f145d66s2".

Lemma ru_element_symbol_nonempty :
  ru_element_symbol <> "".
Proof. discriminate. Qed.

Lemma ru_observed_occupancy_tag_nonempty :
  ru_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma ru_predicted_occupancy_tag_nonempty :
  ru_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma ru_observed_ne_predicted_occupancy :
  ru_observed_occupancy_tag <> ru_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma ru_observed_ne_predicted_subshell :
  ru_observed_subshell_notation <> ru_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma ru_fe_homolog_occupancy_not_copy :
  ru_observed_occupancy_tag <> fe_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Lemma ru_os_homolog_occupancy_not_copy :
  ru_observed_occupancy_tag <> os_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Natural continuum product channel tags                              *)
(* ------------------------------------------------------------------ *)

Definition ore_channel_tag : string := "ore".

Definition isotope_mix_channel_tag : string := "isotope_mix".

Definition purify_refine_channel_tag : string := "purify_refine_cost".

Definition g_stability_channel_tag : string := "g_stability".

Definition env_channel_tag : string := "env".

Lemma ore_channel_tag_nonempty :
  ore_channel_tag <> "".
Proof. discriminate. Qed.

Lemma isotope_mix_channel_tag_nonempty :
  isotope_mix_channel_tag <> "".
Proof. discriminate. Qed.

Lemma purify_refine_channel_tag_nonempty :
  purify_refine_channel_tag <> "".
Proof. discriminate. Qed.

Lemma g_stability_channel_tag_nonempty :
  g_stability_channel_tag <> "".
Proof. discriminate. Qed.

Lemma env_channel_tag_nonempty :
  env_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum product channel — concurrent **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ruec_channel_slot : Type :=
  | ruec_slot_unwired
  | ruec_slot_absent
  | ruec_slot_present.

Definition ruec_channel_slot_beq (s1 s2 : ruec_channel_slot) : bool :=
  match s1, s2 with
  | ruec_slot_unwired, ruec_slot_unwired => true
  | ruec_slot_absent, ruec_slot_absent => true
  | ruec_slot_present, ruec_slot_present => true
  | _, _ => false
  end.

Definition ruec_channel_slot_is_present (s : ruec_channel_slot) : bool :=
  match s with
  | ruec_slot_present => true
  | _ => false
  end.

Definition ruExceptionContinuumProductChannelCount : nat := 5.

Lemma ru_exception_continuum_product_channel_count_is_five :
  ruExceptionContinuumProductChannelCount = 5.
Proof. reflexivity. Qed.

Definition ruec_channel_ore : nat := 0.
Definition ruec_channel_isotope_mix : nat := 1.
Definition ruec_channel_purify_refine : nat := 2.
Definition ruec_channel_g_stability : nat := 3.
Definition ruec_channel_env : nat := 4.

Lemma ruec_channel_ore_idx_is_0 :
  ruec_channel_ore = 0.
Proof. reflexivity. Qed.

Lemma ruec_channel_isotope_mix_idx_is_1 :
  ruec_channel_isotope_mix = 1.
Proof. reflexivity. Qed.

Lemma ruec_channel_purify_refine_idx_is_2 :
  ruec_channel_purify_refine = 2.
Proof. reflexivity. Qed.

Lemma ruec_channel_g_stability_idx_is_3 :
  ruec_channel_g_stability = 3.
Proof. reflexivity. Qed.

Lemma ruec_channel_env_idx_is_4 :
  ruec_channel_env = 4.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum concurrent **product** bundle scaffold       *)
(* ------------------------------------------------------------------ *)

Definition ruec_channel_bundle : Type := nat -> ruec_channel_slot.

Definition ruExceptionContinuumBundleAllUnwired : ruec_channel_bundle :=
  fun _ => ruec_slot_unwired.

Definition ruExceptionContinuumBundleAt (b : ruec_channel_bundle) (idx : nat)
  (slot : ruec_channel_slot) : ruec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition ruExceptionContinuumBundleWithPresent
  (b : ruec_channel_bundle) (idx : nat) : ruec_channel_bundle :=
  ruExceptionContinuumBundleAt b idx ruec_slot_present.

Fixpoint count_ruec_present_up_to (b : ruec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if ruec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_ruec_present_up_to b i + add
  end.

Definition ruExceptionContinuumBundlePresentCount (b : ruec_channel_bundle) : nat :=
  count_ruec_present_up_to b ruExceptionContinuumProductChannelCount.

Definition ruExceptionContinuumBundleHolds (b : ruec_channel_bundle) (idx : nat) : bool :=
  ruec_channel_slot_is_present (b idx).

Definition ruExceptionContinuumBundleIsConcurrentProduct (b : ruec_channel_bundle) : bool :=
  Nat.leb 2 (ruExceptionContinuumBundlePresentCount b).

(* Ru Z=44 natural continuum witness — ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env. *)
Definition ruExceptionContinuumRu44Witness : ruec_channel_bundle :=
  ruExceptionContinuumBundleWithPresent
    (ruExceptionContinuumBundleWithPresent
      (ruExceptionContinuumBundleWithPresent
        (ruExceptionContinuumBundleWithPresent
          (ruExceptionContinuumBundleWithPresent
            ruExceptionContinuumBundleAllUnwired
            ruec_channel_ore)
          ruec_channel_isotope_mix)
        ruec_channel_purify_refine)
      ruec_channel_g_stability)
    ruec_channel_env.

Definition ruExceptionContinuumEmptyWitness : ruec_channel_bundle :=
  ruExceptionContinuumBundleAllUnwired.

Definition ruExceptionContinuumSinglePresent : ruec_channel_bundle :=
  ruExceptionContinuumBundleWithPresent ruExceptionContinuumBundleAllUnwired
    ruec_channel_ore.

Lemma ore_channel_present :
  ruExceptionContinuumBundleHolds ruExceptionContinuumRu44Witness
    ruec_channel_ore = true.
Proof. reflexivity. Qed.

Lemma isotope_mix_channel_present :
  ruExceptionContinuumBundleHolds ruExceptionContinuumRu44Witness
    ruec_channel_isotope_mix = true.
Proof. reflexivity. Qed.

Lemma purify_refine_channel_present :
  ruExceptionContinuumBundleHolds ruExceptionContinuumRu44Witness
    ruec_channel_purify_refine = true.
Proof. reflexivity. Qed.

Lemma g_stability_channel_present :
  ruExceptionContinuumBundleHolds ruExceptionContinuumRu44Witness
    ruec_channel_g_stability = true.
Proof. reflexivity. Qed.

Lemma env_channel_present :
  ruExceptionContinuumBundleHolds ruExceptionContinuumRu44Witness
    ruec_channel_env = true.
Proof. reflexivity. Qed.

Lemma ru44_witness_present_count_is_five :
  ruExceptionContinuumBundlePresentCount ruExceptionContinuumRu44Witness = 5.
Proof. reflexivity. Qed.

Lemma ru44_witness_is_concurrent_product :
  ruExceptionContinuumBundleIsConcurrentProduct ruExceptionContinuumRu44Witness = true.
Proof.
  unfold ruExceptionContinuumBundleIsConcurrentProduct.
  rewrite ru44_witness_present_count_is_five.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  ruExceptionContinuumBundlePresentCount ruExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  ruExceptionContinuumBundleIsConcurrentProduct ruExceptionContinuumEmptyWitness = false.
Proof.
  unfold ruExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  ruExceptionContinuumBundlePresentCount ruExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  ruExceptionContinuumBundleIsConcurrentProduct ruExceptionContinuumSinglePresent = false.
Proof.
  unfold ruExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive ruec_xor_posture : Type :=
  | ruec_xor_exclusive
  | ruec_xor_concurrent_product.

Definition ruecXorClassifierMarker : string := "chem_l0_ru_exception_xor_classifier_v1".
Definition cecConcurrentProductMarker : string := "chem_int_ru_exception_continuum_product_v1".

Lemma ruec_xor_marker_ne_concurrent_product_marker :
  ruecXorClassifierMarker <> cecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition ruecXorClassifierIncompatible (claim_xor : bool)
  (b : ruec_channel_bundle) : bool :=
  claim_xor && ruExceptionContinuumBundleIsConcurrentProduct b.

Lemma ruec_xor_refuse_on_ru44_witness :
  ruecXorClassifierIncompatible true ruExceptionContinuumRu44Witness = true.
Proof.
  unfold ruecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma ruec_xor_ok_on_concurrent_product_claim :
  ruecXorClassifierIncompatible false ruExceptionContinuumRu44Witness = false.
Proof. reflexivity. Qed.

Definition ruecProductNotXor : bool :=
  ruExceptionContinuumBundleIsConcurrentProduct ruExceptionContinuumRu44Witness &&
  ruecXorClassifierIncompatible true ruExceptionContinuumRu44Witness.

Lemma ruec_product_not_xor_true : ruecProductNotXor = true.
Proof.
  unfold ruecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  ruecProductNotXor = true /\
  Nat.leb 2 (ruExceptionContinuumBundlePresentCount
    ruExceptionContinuumRu44Witness) = true /\
  ruecXorClassifierMarker <> cecConcurrentProductMarker.
Proof.
  split.
  - apply ruec_product_not_xor_true.
  - split.
    + rewrite ru44_witness_present_count_is_five.
      reflexivity.
    + apply ruec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum **conservation** bar — Proved-without-bar    *)
(* ------------------------------------------------------------------ *)

Inductive ruec_bar_presence : Type :=
  | ruec_bar_absent
  | ruec_bar_present.

Record ruec_claim_bar : Type := {
  ruec_bar_presence_field : ruec_bar_presence;
  ruec_bar_defect_total : nat
}.

Definition ruExceptionContinuumClaimBarAbsent : ruec_claim_bar :=
  {| ruec_bar_presence_field := ruec_bar_absent;
     ruec_bar_defect_total := 0 |}.

Definition ruExceptionContinuumClaimBarZeroDefect : ruec_claim_bar :=
  {| ruec_bar_presence_field := ruec_bar_present;
     ruec_bar_defect_total := 0 |}.

Definition ruec_claim_bar_zero_defect (b : ruec_claim_bar) : bool :=
  match ruec_bar_presence_field b with
  | ruec_bar_absent => false
  | ruec_bar_present => Nat.eqb (ruec_bar_defect_total b) 0
  end.

Lemma ruec_claim_bar_zero_defect_true :
  ruec_claim_bar_zero_defect ruExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma ruec_claim_bar_absent_not_zero_defect :
  ruec_claim_bar_zero_defect ruExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum **conservation** verdict — fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive ruec_conservation_verdict : Type :=
  | ruec_verdict_unwired_ok
  | ruec_verdict_named_ok
  | ruec_verdict_design_ok
  | ruec_verdict_trivial_refuse
  | ruec_verdict_xor_refuse
  | ruec_verdict_green_invent_refuse
  | ruec_verdict_proved_without_bar_refuse
  | ruec_verdict_production_wired_refuse
  | ruec_verdict_parallel_exception_axiom_refuse
  | ruec_verdict_homolog_copy_refuse
  | ruec_verdict_extra_element_id_refuse
  | ruec_verdict_madelung_family_smuggle_refuse
  | ruec_verdict_tp_float_pin_refuse.

Definition ruec_conservation_verdict_ok (v : ruec_conservation_verdict) : bool :=
  match v with
  | ruec_verdict_unwired_ok => true
  | ruec_verdict_named_ok => true
  | ruec_verdict_design_ok => true
  | _ => false
  end.

Definition ruExceptionContinuumBundleNontrivial (b : ruec_channel_bundle) : bool :=
  Nat.ltb 0 (ruExceptionContinuumBundlePresentCount b).

Definition evaluate_ru_exception_continuum_bundle
  (m : RuExceptionContinuumModality)
  (b : ruec_channel_bundle)
  (bar : ruec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : ruec_conservation_verdict :=
  if claim_physics_green
  then ruec_verdict_green_invent_refuse
  else if claim_proved
       then ruec_verdict_proved_without_bar_refuse
       else if negb (ruExceptionContinuumBundleNontrivial b)
            then ruec_verdict_trivial_refuse
            else if ruecXorClassifierIncompatible claim_xor_classifier b
                 then ruec_verdict_xor_refuse
                 else
                   match m with
                   | ru_exception_continuum_unwired =>
                       if ruExceptionContinuumBundleIsConcurrentProduct b
                       then ruec_verdict_named_ok
                       else ruec_verdict_design_ok
                   | ru_exception_continuum_assumed
                   | ru_exception_continuum_surrogate =>
                       ruec_verdict_design_ok
                   | ru_exception_continuum_proved =>
                       ruec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_ru_exception_continuum_close
  (m : RuExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : ruec_conservation_verdict :=
  if claim_physics_green
  then ruec_verdict_green_invent_refuse
  else if claim_production_wired
  then ruec_verdict_production_wired_refuse
  else
    match m with
    | ru_exception_continuum_unwired => ruec_verdict_unwired_ok
    | ru_exception_continuum_assumed
    | ru_exception_continuum_proved
    | ru_exception_continuum_surrogate => ruec_verdict_named_ok
    end.

Definition ru_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_ru_exception_continuum_close
          ru_exception_continuum_proved claim_physics_green claim_production_wired with
  | ruec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive ruec_conservation_law : Type :=
  | ruec_law_conserved
  | ruec_law_named_ok
  | ruec_law_trivial_refuse
  | ruec_law_green_invent_refuse.

Definition ruec_conservation_law_count : nat := 4.

Lemma ruec_conservation_law_count_is_four :
  ruec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive ruec_conservation_law_witness : Type :=
  | ruec_law_witness_open
  | ruec_law_witness_proved.

Definition evaluate_ruec_conservation_law_witness
  (law : ruec_conservation_law)
  (m : RuExceptionContinuumModality)
  : ruec_conservation_law_witness :=
  match m with
  | ru_exception_continuum_unwired
  | ru_exception_continuum_assumed
  | ru_exception_continuum_surrogate => ruec_law_witness_open
  | ru_exception_continuum_proved => ruec_law_witness_proved
  end.

Lemma all_ruec_conservation_laws_open_at_unwired :
  evaluate_ruec_conservation_law_witness ruec_law_conserved
    ru_exception_continuum_unwired = ruec_law_witness_open /\
  evaluate_ruec_conservation_law_witness ruec_law_named_ok
    ru_exception_continuum_unwired = ruec_law_witness_open /\
  evaluate_ruec_conservation_law_witness ruec_law_trivial_refuse
    ru_exception_continuum_unwired = ruec_law_witness_open /\
  evaluate_ruec_conservation_law_witness ruec_law_green_invent_refuse
    ru_exception_continuum_unwired = ruec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum pins (structure witnesses — not Proved)      *)
(* ------------------------------------------------------------------ *)

Definition ruExceptionContinuumProved : bool := false.

Lemma ru_exception_continuum_proved_false :
  ruExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_unwired false false =
  ruec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_unwired false false =
  ruec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_unwired false false) =
  true.
Proof.
  unfold ruec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Ru Z=44 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma ru44_witness_named_ok :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false false =
  ruec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ru44_exception_continuum :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false false =
  ruec_verdict_named_ok /\
  ruExceptionContinuumBundleIsConcurrentProduct ruExceptionContinuumRu44Witness = true /\
  ruthenium_atomic_number_z = 44 /\
  ru_observed_occupancy_tag = "4d75s1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma ruec_named_close_ok :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_proved false false =
  ruec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_ru_exception_continuum_close :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_proved false false =
  ruec_verdict_named_ok /\
  ru_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply ruec_named_close_ok.
  - unfold ru_exception_continuum_authorized.
    rewrite ruec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumEmptyWitness
    ruExceptionContinuumClaimBarAbsent false false false =
  ruec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumEmptyWitness
    ruExceptionContinuumClaimBarAbsent false false false =
  ruec_verdict_trivial_refuse /\
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_bundle
       ru_exception_continuum_unwired
       ruExceptionContinuumEmptyWitness
       ruExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold ruec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent true false false =
  ruec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent true false false =
  ruec_verdict_xor_refuse /\
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_bundle
       ru_exception_continuum_unwired
       ruExceptionContinuumRu44Witness
       ruExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold ruec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_unwired true false =
  ruec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_unwired true false) =
  false.
Proof.
  unfold ruec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_ruec_bundle_refuse :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false true false =
  ruec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false true =
  ruec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false true =
  ruec_verdict_proved_without_bar_refuse /\
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_bundle
       ru_exception_continuum_unwired
       ruExceptionContinuumRu44Witness
       ruExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold ruec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — WAVE100 not wired lib.rs                  *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_proved false true =
  ruec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_proved false true) =
  false.
Proof.
  unfold ruec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel exception axiom refuse — not 26th periodic-table axiom     *)
(* ------------------------------------------------------------------ *)

Definition ruExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_exception_axiom_refuse :
  ruExceptionContinuumAuthority <>
  parallelExceptionAxiomTag /\
  ruExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply ru_exception_continuum_proved_false.
Qed.

Theorem parallel_exception_axiom_not_minted :
  ruExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  ruExceptionContinuumProved = false /\
  ruExceptionContinuumAuthority <> parallelExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog copy refuse — Ta Z=73 occupancy ≠ Ru Z=44 copy              *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "fe_z26_occupancy_copied_onto_ru_z44".

Definition osHomologCopyFraming : string :=
  "os_z76_occupancy_copied_onto_ru_z44".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition ruExceptionContinuumFraming : string :=
  "second_law_conservation_occupancy_engine_sort_ru_z44_one_axiom".

Lemma homolog_copy_refuse :
  ruExceptionContinuumFraming <>
  homologCopyFraming /\
  ru_observed_occupancy_tag <> fe_homolog_observed_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply ru_fe_homolog_occupancy_not_copy.
Qed.

Theorem ru_fe_os_homolog_not_occupancy_copy :
  ruExceptionContinuumFraming <>
  homologCopyFraming /\
  ruExceptionContinuumFraming <>
  osHomologCopyFraming /\
  ruthenium_atomic_number_z = 44 /\
  iron_homolog_z = 26 /\
  osmium_homolog_z = 76 /\
  ru_observed_occupancy_tag <> fe_homolog_observed_occupancy_tag /\
  ru_observed_occupancy_tag <> os_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — Ru exception ≠ Z=119 smuggle               *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "ru_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  ruExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem ru_exception_not_extra_element_id :
  ruExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  ruthenium_atomic_number_z = 44.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Madelung family smuggle refuse — observed override ≠ family-only      *)
(* ------------------------------------------------------------------ *)

Definition madelungFamilySmuggleFraming : string :=
  "madelung_family_only_no_observed_override".

Definition madelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Lemma madelung_family_smuggle_refuse :
  ruExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  ru_observed_occupancy_tag <> ru_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply ru_observed_ne_predicted_occupancy.
Qed.

Theorem ru_observed_override_not_madelung_family_smuggle :
  ruExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  ru_observed_occupancy_tag = "4d75s1" /\
  ru_predicted_occupancy_tag = "4d65s2" /\
  ruExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions ≠ bare float pins            *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_ru_exception_scaffold".

Lemma tp_float_pin_refuse :
  ruExceptionContinuumFraming <>
  tpFloatPinFraming /\
  g_stability_channel_tag = "g_stability".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  ruExceptionContinuumFraming <>
  tpFloatPinFraming /\
  env_channel_tag = "env" /\
  ruthenium_atomic_number_z = 44.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ru exception continuum coherence scaffold                             *)
(* ------------------------------------------------------------------ *)

Definition ruec_conservation_coherence_scaffold : bool :=
  ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_proved false false) &&
  negb (ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_unwired true false)) &&
  negb (ruec_conservation_verdict_ok
    (evaluate_ru_exception_continuum_close
       ru_exception_continuum_proved false true)).

Lemma ruec_conservation_coherence_scaffold_true :
  ruec_conservation_coherence_scaffold = true.
Proof.
  unfold ruec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem ruec_conservation_coherence_scaffold_theorem :
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_proved false false =
    ruec_verdict_named_ok /\
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_unwired true false =
    ruec_verdict_green_invent_refuse /\
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_proved false true =
    ruec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition ruec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition ruec_conservation_knowing_fiber_ok : bool :=
  ruec_conservation_fiber_ok fiber_quantum_knowing.

Definition ruec_conservation_meso_acting_ok : bool :=
  ruec_conservation_fiber_ok fiber_meso_acting.

Lemma ruec_conservation_knowing_fiber_ok_true :
  ruec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma ruec_conservation_meso_acting_not_ok :
  ruec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem ruec_conservation_routes_knowing_not_meso :
  ruec_conservation_knowing_fiber_ok = true /\
  ruec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply ruec_conservation_knowing_fiber_ok_true.
  - apply ruec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  ruec_conservation_knowing_fiber_ok &&
  negb ruec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, ruec_conservation_knowing_fiber_ok,
    ruec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named Ru Z=44 + fail-closed + fiber              *)
(* ------------------------------------------------------------------ *)

Theorem ru_exception_continuum_fixture_scaffold :
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false false =
    ruec_verdict_named_ok /\
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumEmptyWitness
    ruExceptionContinuumClaimBarAbsent false false false =
    ruec_verdict_trivial_refuse /\
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent true false false =
    ruec_verdict_xor_refuse /\
  evaluate_ru_exception_continuum_bundle
    ru_exception_continuum_unwired
    ruExceptionContinuumRu44Witness
    ruExceptionContinuumClaimBarAbsent false false true =
    ruec_verdict_proved_without_bar_refuse /\
  evaluate_ru_exception_continuum_close
    ru_exception_continuum_unwired false false =
    ruec_verdict_unwired_ok /\
  ruec_conservation_knowing_fiber_ok = true /\
  ruec_conservation_meso_acting_ok = false /\
  ruExceptionContinuumProved = false /\
  ruecProductNotXor = true /\
  ruthenium_atomic_number_z = 44.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — read-only cite)      *)
(* ------------------------------------------------------------------ *)

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/OccupancyEngineSort.v".

Definition goldschmidtConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/GoldschmidtConservation.v".

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Definition ruExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-RU-EXCEPTION-CONTINUUM".

Definition ruExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-RU-EXCEPTION-CONTINUUM RuExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice ruExceptionContinuumProved false evaluateRuExceptionContinuumBundle evaluateRuExceptionContinuumClose named Ru Z=44 4d4 5s1 occupancy engine sort dblock_exception ore isotope purify G env concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel exception axiom refuse homolog copy refuse Fe Z=26 Os Z=76 extra element id Z=119 refuse madelung family smuggle refuse Ru ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 not lib.rs".

Lemma ru_exception_continuum_cell_id :
  ruExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-RU-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma ru_exception_continuum_cites_dblock_exceptions :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma ru_exception_continuum_cites_occupancy_engine_sort :
  occupancyEngineSortAuthority <> "".
Proof. discriminate. Qed.

Lemma ru_exception_continuum_cites_goldschmidt :
  goldschmidtConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma ru_exception_continuum_cites_homolog_not_copy :
  homologExceptionNotCopyAuthority <>
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma ru_exception_continuum_cites_homolog_cell :
  homologExceptionNotCopyCellId =
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".
Proof. reflexivity. Qed.


Definition z044RuAuthority : string :=
  "umst/umst-chem/src/elements/z_044_ru.rs".

Lemma ru_exception_continuum_cites_z_044_ru :
  z044RuAuthority =
  "umst/umst-chem/src/elements/z_044_ru.rs".
Proof. reflexivity. Qed.

Lemma ru_exception_continuum_cites_madelung_witness :
  madelungWitnessAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma ru_exception_not_26th_axiom :
  ruExceptionContinuumFraming <> parallelExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma ru_exception_second_law_conservation_framing :
  ruExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort — Ru sorts dblock_exception bucket            *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition occupancyEngineSortFraming : string :=
  "occupancy_engine_sort_dblock_exception_bucket".

Lemma ru_sorts_dblock_exception_bucket :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Lemma ru_exception_continuum_cites_occupancy_engine_sort_int :
  occupancyEngineSortIntAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Theorem ru_occupancy_engine_sort_not_new_axiom :
  occupancyEngineSortFraming <>
  parallelExceptionAxiomTag /\
  occupancyEngineSortBucketTag = "dblock_exception" /\
  ruExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  split; [apply ru_sorts_dblock_exception_bucket | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma ru_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma ru_exception_continuum_modality_unwired :
  ruExceptionContinuumModalityCurrent =
  ru_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition ruExceptionContinuumProductionWired : Prop := False.

Lemma ru_exception_continuum_not_production_wired :
  ~ ruExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

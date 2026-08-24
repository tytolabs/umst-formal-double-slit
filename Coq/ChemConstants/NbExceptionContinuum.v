(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: NbExceptionContinuum.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: Nb Z=41 4d⁴5s¹ **exception continuum**.          *)
(*  D-block Madelung occupancy exception as occupancy-engine sort on    *)
(*  the same second-law + conservation object (ore ⊗ isotope ⊗ purify  *)
(*  ⊗ G-stability ⊗ Env concurrent product — not XOR enum).            *)
(*  Not a 26th periodic-table axiom; homolog ≠ occupancy copy (Ta Z=73  *)
(*  same group, distinct observed override). nbExceptionContinuumProved  *)
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
(*  Nb exception continuum modality (Unwired / Assumed / Proved /       *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive NbExceptionContinuumModality : Type :=
  | nb_exception_continuum_unwired
  | nb_exception_continuum_assumed
  | nb_exception_continuum_proved
  | nb_exception_continuum_surrogate.

Definition nbExceptionContinuumModalityCurrent : NbExceptionContinuumModality :=
  nb_exception_continuum_unwired.

Definition nb_exception_continuum_lattice_cardinality : nat := 4.

Lemma nb_exception_continuum_lattice_cardinality_is_four :
  nb_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma nb_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb nb_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold nb_exception_continuum_lattice_cardinality.
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
(*  IUPAC Z pins — Nb Z=41 d-block exception witness                   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition niobium_atomic_number_z : nat := 41.

Lemma niobium_atomic_number_z_is_41 :
  niobium_atomic_number_z = 41.
Proof. reflexivity. Qed.

Definition tantalum_homolog_z : nat := 73.

Lemma tantalum_homolog_z_is_73 :
  tantalum_homolog_z = 73.
Proof. reflexivity. Qed.

Definition niobium_z_valid : bool :=
  Nat.ltb 0 niobium_atomic_number_z &&
  Nat.leb niobium_atomic_number_z iupac_table_cardinality.

Lemma niobium_z_valid_true : niobium_z_valid = true.
Proof.
  unfold niobium_z_valid, niobium_atomic_number_z, iupac_table_cardinality.
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
(*  Nb Z=41 occupancy pins — 4d⁴5s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition nb_element_symbol : string := "Nb".

Definition nb_observed_occupancy_tag : string := "4d45s1".

Definition nb_predicted_occupancy_tag : string := "5s24d3".

Definition nb_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s14d4".

Definition nb_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d3".

Definition ta_homolog_observed_occupancy_tag : string := "4f145d36s2".

Lemma nb_element_symbol_nonempty :
  nb_element_symbol <> "".
Proof. discriminate. Qed.

Lemma nb_observed_occupancy_tag_nonempty :
  nb_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma nb_predicted_occupancy_tag_nonempty :
  nb_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma nb_observed_ne_predicted_occupancy :
  nb_observed_occupancy_tag <> nb_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma nb_observed_ne_predicted_subshell :
  nb_observed_subshell_notation <> nb_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma nb_homolog_occupancy_not_copy :
  nb_observed_occupancy_tag <> ta_homolog_observed_occupancy_tag.
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
(*  Nb exception continuum product channel — concurrent **product**     *)
(* ------------------------------------------------------------------ *)

Inductive nec_channel_slot : Type :=
  | nec_slot_unwired
  | nec_slot_absent
  | nec_slot_present.

Definition nec_channel_slot_beq (s1 s2 : nec_channel_slot) : bool :=
  match s1, s2 with
  | nec_slot_unwired, nec_slot_unwired => true
  | nec_slot_absent, nec_slot_absent => true
  | nec_slot_present, nec_slot_present => true
  | _, _ => false
  end.

Definition nec_channel_slot_is_present (s : nec_channel_slot) : bool :=
  match s with
  | nec_slot_present => true
  | _ => false
  end.

Definition nbExceptionContinuumProductChannelCount : nat := 5.

Lemma nb_exception_continuum_product_channel_count_is_five :
  nbExceptionContinuumProductChannelCount = 5.
Proof. reflexivity. Qed.

Definition nec_channel_ore : nat := 0.
Definition nec_channel_isotope_mix : nat := 1.
Definition nec_channel_purify_refine : nat := 2.
Definition nec_channel_g_stability : nat := 3.
Definition nec_channel_env : nat := 4.

Lemma nec_channel_ore_idx_is_0 :
  nec_channel_ore = 0.
Proof. reflexivity. Qed.

Lemma nec_channel_isotope_mix_idx_is_1 :
  nec_channel_isotope_mix = 1.
Proof. reflexivity. Qed.

Lemma nec_channel_purify_refine_idx_is_2 :
  nec_channel_purify_refine = 2.
Proof. reflexivity. Qed.

Lemma nec_channel_g_stability_idx_is_3 :
  nec_channel_g_stability = 3.
Proof. reflexivity. Qed.

Lemma nec_channel_env_idx_is_4 :
  nec_channel_env = 4.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum concurrent **product** bundle scaffold       *)
(* ------------------------------------------------------------------ *)

Definition nec_channel_bundle : Type := nat -> nec_channel_slot.

Definition nbExceptionContinuumBundleAllUnwired : nec_channel_bundle :=
  fun _ => nec_slot_unwired.

Definition nbExceptionContinuumBundleAt (b : nec_channel_bundle) (idx : nat)
  (slot : nec_channel_slot) : nec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition nbExceptionContinuumBundleWithPresent
  (b : nec_channel_bundle) (idx : nat) : nec_channel_bundle :=
  nbExceptionContinuumBundleAt b idx nec_slot_present.

Fixpoint count_nec_present_up_to (b : nec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if nec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_nec_present_up_to b i + add
  end.

Definition nbExceptionContinuumBundlePresentCount (b : nec_channel_bundle) : nat :=
  count_nec_present_up_to b nbExceptionContinuumProductChannelCount.

Definition nbExceptionContinuumBundleHolds (b : nec_channel_bundle) (idx : nat) : bool :=
  nec_channel_slot_is_present (b idx).

Definition nbExceptionContinuumBundleIsConcurrentProduct (b : nec_channel_bundle) : bool :=
  Nat.leb 2 (nbExceptionContinuumBundlePresentCount b).

(* Nb Z=41 natural continuum witness — ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env. *)
Definition nbExceptionContinuumNb41Witness : nec_channel_bundle :=
  nbExceptionContinuumBundleWithPresent
    (nbExceptionContinuumBundleWithPresent
      (nbExceptionContinuumBundleWithPresent
        (nbExceptionContinuumBundleWithPresent
          (nbExceptionContinuumBundleWithPresent
            nbExceptionContinuumBundleAllUnwired
            nec_channel_ore)
          nec_channel_isotope_mix)
        nec_channel_purify_refine)
      nec_channel_g_stability)
    nec_channel_env.

Definition nbExceptionContinuumEmptyWitness : nec_channel_bundle :=
  nbExceptionContinuumBundleAllUnwired.

Definition nbExceptionContinuumSinglePresent : nec_channel_bundle :=
  nbExceptionContinuumBundleWithPresent nbExceptionContinuumBundleAllUnwired
    nec_channel_ore.

Lemma ore_channel_present :
  nbExceptionContinuumBundleHolds nbExceptionContinuumNb41Witness
    nec_channel_ore = true.
Proof. reflexivity. Qed.

Lemma isotope_mix_channel_present :
  nbExceptionContinuumBundleHolds nbExceptionContinuumNb41Witness
    nec_channel_isotope_mix = true.
Proof. reflexivity. Qed.

Lemma purify_refine_channel_present :
  nbExceptionContinuumBundleHolds nbExceptionContinuumNb41Witness
    nec_channel_purify_refine = true.
Proof. reflexivity. Qed.

Lemma g_stability_channel_present :
  nbExceptionContinuumBundleHolds nbExceptionContinuumNb41Witness
    nec_channel_g_stability = true.
Proof. reflexivity. Qed.

Lemma env_channel_present :
  nbExceptionContinuumBundleHolds nbExceptionContinuumNb41Witness
    nec_channel_env = true.
Proof. reflexivity. Qed.

Lemma nb41_witness_present_count_is_five :
  nbExceptionContinuumBundlePresentCount nbExceptionContinuumNb41Witness = 5.
Proof. reflexivity. Qed.

Lemma nb41_witness_is_concurrent_product :
  nbExceptionContinuumBundleIsConcurrentProduct nbExceptionContinuumNb41Witness = true.
Proof.
  unfold nbExceptionContinuumBundleIsConcurrentProduct.
  rewrite nb41_witness_present_count_is_five.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  nbExceptionContinuumBundlePresentCount nbExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  nbExceptionContinuumBundleIsConcurrentProduct nbExceptionContinuumEmptyWitness = false.
Proof.
  unfold nbExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  nbExceptionContinuumBundlePresentCount nbExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  nbExceptionContinuumBundleIsConcurrentProduct nbExceptionContinuumSinglePresent = false.
Proof.
  unfold nbExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive nec_xor_posture : Type :=
  | nec_xor_exclusive
  | nec_xor_concurrent_product.

Definition cecXorClassifierMarker : string := "chem_l0_nb_exception_xor_classifier_v1".
Definition cecConcurrentProductMarker : string := "chem_int_nb_exception_continuum_product_v1".

Lemma nec_xor_marker_ne_concurrent_product_marker :
  cecXorClassifierMarker <> cecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition cecXorClassifierIncompatible (claim_xor : bool)
  (b : nec_channel_bundle) : bool :=
  claim_xor && nbExceptionContinuumBundleIsConcurrentProduct b.

Lemma nec_xor_refuse_on_nb41_witness :
  cecXorClassifierIncompatible true nbExceptionContinuumNb41Witness = true.
Proof.
  unfold cecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma nec_xor_ok_on_concurrent_product_claim :
  cecXorClassifierIncompatible false nbExceptionContinuumNb41Witness = false.
Proof. reflexivity. Qed.

Definition cecProductNotXor : bool :=
  nbExceptionContinuumBundleIsConcurrentProduct nbExceptionContinuumNb41Witness &&
  cecXorClassifierIncompatible true nbExceptionContinuumNb41Witness.

Lemma nec_product_not_xor_true : cecProductNotXor = true.
Proof.
  unfold cecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  cecProductNotXor = true /\
  Nat.leb 2 (nbExceptionContinuumBundlePresentCount
    nbExceptionContinuumNb41Witness) = true /\
  cecXorClassifierMarker <> cecConcurrentProductMarker.
Proof.
  split.
  - apply nec_product_not_xor_true.
  - split.
    + rewrite nb41_witness_present_count_is_five.
      reflexivity.
    + apply nec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum **conservation** bar — Proved-without-bar    *)
(* ------------------------------------------------------------------ *)

Inductive nec_bar_presence : Type :=
  | nec_bar_absent
  | nec_bar_present.

Record nec_claim_bar : Type := {
  nec_bar_presence_field : nec_bar_presence;
  nec_bar_defect_total : nat
}.

Definition nbExceptionContinuumClaimBarAbsent : nec_claim_bar :=
  {| nec_bar_presence_field := nec_bar_absent;
     nec_bar_defect_total := 0 |}.

Definition nbExceptionContinuumClaimBarZeroDefect : nec_claim_bar :=
  {| nec_bar_presence_field := nec_bar_present;
     nec_bar_defect_total := 0 |}.

Definition nec_claim_bar_zero_defect (b : nec_claim_bar) : bool :=
  match nec_bar_presence_field b with
  | nec_bar_absent => false
  | nec_bar_present => Nat.eqb (nec_bar_defect_total b) 0
  end.

Lemma nec_claim_bar_zero_defect_true :
  nec_claim_bar_zero_defect nbExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma nec_claim_bar_absent_not_zero_defect :
  nec_claim_bar_zero_defect nbExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum **conservation** verdict — fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive nec_conservation_verdict : Type :=
  | nec_verdict_unwired_ok
  | nec_verdict_named_ok
  | nec_verdict_design_ok
  | nec_verdict_trivial_refuse
  | nec_verdict_xor_refuse
  | nec_verdict_green_invent_refuse
  | nec_verdict_proved_without_bar_refuse
  | nec_verdict_production_wired_refuse
  | nec_verdict_parallel_exception_axiom_refuse
  | nec_verdict_homolog_copy_refuse
  | nec_verdict_extra_element_id_refuse
  | nec_verdict_madelung_family_smuggle_refuse
  | nec_verdict_tp_float_pin_refuse.

Definition nec_conservation_verdict_ok (v : nec_conservation_verdict) : bool :=
  match v with
  | nec_verdict_unwired_ok => true
  | nec_verdict_named_ok => true
  | nec_verdict_design_ok => true
  | _ => false
  end.

Definition nbExceptionContinuumBundleNontrivial (b : nec_channel_bundle) : bool :=
  Nat.ltb 0 (nbExceptionContinuumBundlePresentCount b).

Definition evaluate_nb_exception_continuum_bundle
  (m : NbExceptionContinuumModality)
  (b : nec_channel_bundle)
  (bar : nec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : nec_conservation_verdict :=
  if claim_physics_green
  then nec_verdict_green_invent_refuse
  else if claim_proved
       then nec_verdict_proved_without_bar_refuse
       else if negb (nbExceptionContinuumBundleNontrivial b)
            then nec_verdict_trivial_refuse
            else if cecXorClassifierIncompatible claim_xor_classifier b
                 then nec_verdict_xor_refuse
                 else
                   match m with
                   | nb_exception_continuum_unwired =>
                       if nbExceptionContinuumBundleIsConcurrentProduct b
                       then nec_verdict_named_ok
                       else nec_verdict_design_ok
                   | nb_exception_continuum_assumed
                   | nb_exception_continuum_surrogate =>
                       nec_verdict_design_ok
                   | nb_exception_continuum_proved =>
                       nec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_nb_exception_continuum_close
  (m : NbExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : nec_conservation_verdict :=
  if claim_physics_green
  then nec_verdict_green_invent_refuse
  else if claim_production_wired
  then nec_verdict_production_wired_refuse
  else
    match m with
    | nb_exception_continuum_unwired => nec_verdict_unwired_ok
    | nb_exception_continuum_assumed
    | nb_exception_continuum_proved
    | nb_exception_continuum_surrogate => nec_verdict_named_ok
    end.

Definition nb_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_nb_exception_continuum_close
          nb_exception_continuum_proved claim_physics_green claim_production_wired with
  | nec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive nec_conservation_law : Type :=
  | nec_law_conserved
  | nec_law_named_ok
  | nec_law_trivial_refuse
  | nec_law_green_invent_refuse.

Definition nec_conservation_law_count : nat := 4.

Lemma nec_conservation_law_count_is_four :
  nec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive nec_conservation_law_witness : Type :=
  | nec_law_witness_open
  | nec_law_witness_proved.

Definition evaluate_nec_conservation_law_witness
  (law : nec_conservation_law)
  (m : NbExceptionContinuumModality)
  : nec_conservation_law_witness :=
  match m with
  | nb_exception_continuum_unwired
  | nb_exception_continuum_assumed
  | nb_exception_continuum_surrogate => nec_law_witness_open
  | nb_exception_continuum_proved => nec_law_witness_proved
  end.

Lemma all_nec_conservation_laws_open_at_unwired :
  evaluate_nec_conservation_law_witness nec_law_conserved
    nb_exception_continuum_unwired = nec_law_witness_open /\
  evaluate_nec_conservation_law_witness nec_law_named_ok
    nb_exception_continuum_unwired = nec_law_witness_open /\
  evaluate_nec_conservation_law_witness nec_law_trivial_refuse
    nb_exception_continuum_unwired = nec_law_witness_open /\
  evaluate_nec_conservation_law_witness nec_law_green_invent_refuse
    nb_exception_continuum_unwired = nec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum pins (structure witnesses — not Proved)      *)
(* ------------------------------------------------------------------ *)

Definition nbExceptionContinuumProved : bool := false.

Lemma nb_exception_continuum_proved_false :
  nbExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_unwired false false =
  nec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_unwired false false =
  nec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_unwired false false) =
  true.
Proof.
  unfold nec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Nb Z=41 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma nb41_witness_named_ok :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false false =
  nec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_nb41_exception_continuum :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false false =
  nec_verdict_named_ok /\
  nbExceptionContinuumBundleIsConcurrentProduct nbExceptionContinuumNb41Witness = true /\
  niobium_atomic_number_z = 41 /\
  nb_observed_occupancy_tag = "4d45s1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma nec_named_close_ok :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_proved false false =
  nec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_nb_exception_continuum_close :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_proved false false =
  nec_verdict_named_ok /\
  nb_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply nec_named_close_ok.
  - unfold nb_exception_continuum_authorized.
    rewrite nec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumEmptyWitness
    nbExceptionContinuumClaimBarAbsent false false false =
  nec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumEmptyWitness
    nbExceptionContinuumClaimBarAbsent false false false =
  nec_verdict_trivial_refuse /\
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_bundle
       nb_exception_continuum_unwired
       nbExceptionContinuumEmptyWitness
       nbExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold nec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent true false false =
  nec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent true false false =
  nec_verdict_xor_refuse /\
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_bundle
       nb_exception_continuum_unwired
       nbExceptionContinuumNb41Witness
       nbExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold nec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_unwired true false =
  nec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_unwired true false) =
  false.
Proof.
  unfold nec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_nec_bundle_refuse :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false true false =
  nec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false true =
  nec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false true =
  nec_verdict_proved_without_bar_refuse /\
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_bundle
       nb_exception_continuum_unwired
       nbExceptionContinuumNb41Witness
       nbExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold nec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — WAVE100 not wired lib.rs                  *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_proved false true =
  nec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_proved false true) =
  false.
Proof.
  unfold nec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel exception axiom refuse — not 26th periodic-table axiom     *)
(* ------------------------------------------------------------------ *)

Definition nbExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_exception_axiom_refuse :
  nbExceptionContinuumAuthority <>
  parallelExceptionAxiomTag /\
  nbExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply nb_exception_continuum_proved_false.
Qed.

Theorem parallel_exception_axiom_not_minted :
  nbExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  nbExceptionContinuumProved = false /\
  nbExceptionContinuumAuthority <> parallelExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog copy refuse — Ta Z=73 occupancy ≠ Nb Z=41 copy              *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "ta_z73_occupancy_copied_onto_nb_z41".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition nbExceptionContinuumFraming : string :=
  "second_law_conservation_occupancy_engine_sort_nb_z41_one_axiom".

Lemma homolog_copy_refuse :
  nbExceptionContinuumFraming <>
  homologCopyFraming /\
  nb_observed_occupancy_tag <> ta_homolog_observed_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply nb_homolog_occupancy_not_copy.
Qed.

Theorem nb_ta_homolog_not_occupancy_copy :
  nbExceptionContinuumFraming <>
  homologCopyFraming /\
  niobium_atomic_number_z = 41 /\
  tantalum_homolog_z = 73 /\
  nb_observed_occupancy_tag <> ta_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — Nb exception ≠ Z=119 smuggle               *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "nb_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  nbExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem nb_exception_not_extra_element_id :
  nbExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  niobium_atomic_number_z = 41.
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
  nbExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  nb_observed_occupancy_tag <> nb_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply nb_observed_ne_predicted_occupancy.
Qed.

Theorem nb_observed_override_not_madelung_family_smuggle :
  nbExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  nb_observed_occupancy_tag = "4d45s1" /\
  nb_predicted_occupancy_tag = "5s24d3" /\
  nbExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions ≠ bare float pins            *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_nb_exception_scaffold".

Lemma tp_float_pin_refuse :
  nbExceptionContinuumFraming <>
  tpFloatPinFraming /\
  g_stability_channel_tag = "g_stability".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  nbExceptionContinuumFraming <>
  tpFloatPinFraming /\
  env_channel_tag = "env" /\
  niobium_atomic_number_z = 41.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Nb exception continuum coherence scaffold                             *)
(* ------------------------------------------------------------------ *)

Definition nec_conservation_coherence_scaffold : bool :=
  nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_proved false false) &&
  negb (nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_unwired true false)) &&
  negb (nec_conservation_verdict_ok
    (evaluate_nb_exception_continuum_close
       nb_exception_continuum_proved false true)).

Lemma nec_conservation_coherence_scaffold_true :
  nec_conservation_coherence_scaffold = true.
Proof.
  unfold nec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem nec_conservation_coherence_scaffold_theorem :
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_proved false false =
    nec_verdict_named_ok /\
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_unwired true false =
    nec_verdict_green_invent_refuse /\
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_proved false true =
    nec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition nec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition nec_conservation_knowing_fiber_ok : bool :=
  nec_conservation_fiber_ok fiber_quantum_knowing.

Definition nec_conservation_meso_acting_ok : bool :=
  nec_conservation_fiber_ok fiber_meso_acting.

Lemma nec_conservation_knowing_fiber_ok_true :
  nec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma nec_conservation_meso_acting_not_ok :
  nec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem nec_conservation_routes_knowing_not_meso :
  nec_conservation_knowing_fiber_ok = true /\
  nec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply nec_conservation_knowing_fiber_ok_true.
  - apply nec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  nec_conservation_knowing_fiber_ok &&
  negb nec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, nec_conservation_knowing_fiber_ok,
    nec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named Nb Z=41 + fail-closed + fiber              *)
(* ------------------------------------------------------------------ *)

Theorem nb_exception_continuum_fixture_scaffold :
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false false =
    nec_verdict_named_ok /\
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumEmptyWitness
    nbExceptionContinuumClaimBarAbsent false false false =
    nec_verdict_trivial_refuse /\
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent true false false =
    nec_verdict_xor_refuse /\
  evaluate_nb_exception_continuum_bundle
    nb_exception_continuum_unwired
    nbExceptionContinuumNb41Witness
    nbExceptionContinuumClaimBarAbsent false false true =
    nec_verdict_proved_without_bar_refuse /\
  evaluate_nb_exception_continuum_close
    nb_exception_continuum_unwired false false =
    nec_verdict_unwired_ok /\
  nec_conservation_knowing_fiber_ok = true /\
  nec_conservation_meso_acting_ok = false /\
  nbExceptionContinuumProved = false /\
  cecProductNotXor = true /\
  niobium_atomic_number_z = 41.
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

Definition nbExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-NB-EXCEPTION-CONTINUUM".

Definition nbExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-NB-EXCEPTION-CONTINUUM NbExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice nbExceptionContinuumProved false evaluateNbExceptionContinuumBundle evaluateNbExceptionContinuumClose named Nb Z=41 4d4 5s1 occupancy engine sort dblock_exception ore isotope purify G env concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel exception axiom refuse homolog copy refuse Ta Z=73 extra element id Z=119 refuse madelung family smuggle refuse Nb ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 not lib.rs".

Lemma nb_exception_continuum_cell_id :
  nbExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-NB-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma nb_exception_continuum_cites_dblock_exceptions :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma nb_exception_continuum_cites_occupancy_engine_sort :
  occupancyEngineSortAuthority <> "".
Proof. discriminate. Qed.

Lemma nb_exception_continuum_cites_goldschmidt :
  goldschmidtConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma nb_exception_continuum_cites_homolog_not_copy :
  homologExceptionNotCopyAuthority <>
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma nb_exception_continuum_cites_homolog_cell :
  homologExceptionNotCopyCellId =
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".
Proof. reflexivity. Qed.

Lemma nb_exception_continuum_cites_madelung_witness :
  madelungWitnessAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma nb_exception_not_26th_axiom :
  nbExceptionContinuumFraming <> parallelExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma nb_exception_second_law_conservation_framing :
  nbExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort — Nb sorts dblock_exception bucket            *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition occupancyEngineSortFraming : string :=
  "occupancy_engine_sort_dblock_exception_bucket".

Lemma nb_sorts_dblock_exception_bucket :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Lemma nb_exception_continuum_cites_occupancy_engine_sort_int :
  occupancyEngineSortIntAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Theorem nb_occupancy_engine_sort_not_new_axiom :
  occupancyEngineSortFraming <>
  parallelExceptionAxiomTag /\
  occupancyEngineSortBucketTag = "dblock_exception" /\
  nbExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  split; [apply nb_sorts_dblock_exception_bucket | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma nb_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma nb_exception_continuum_modality_unwired :
  nbExceptionContinuumModalityCurrent =
  nb_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition nbExceptionContinuumProductionWired : Prop := False.

Lemma nb_exception_continuum_not_production_wired :
  ~ nbExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

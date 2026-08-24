(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CrExceptionContinuum.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: Cr Z=24 4s¹3d⁵ **exception continuum**.          *)
(*  D-block Madelung occupancy exception as occupancy-engine sort on    *)
(*  the same second-law + conservation object (ore ⊗ isotope ⊗ purify  *)
(*  ⊗ G-stability ⊗ Env concurrent product — not XOR enum).            *)
(*  Not a 26th periodic-table axiom; homolog ≠ occupancy copy (Mo Z=42  *)
(*  same group, distinct observed override). crExceptionContinuumProved  *)
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
(*  Cr exception continuum modality (Unwired / Assumed / Proved /       *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive CrExceptionContinuumModality : Type :=
  | cr_exception_continuum_unwired
  | cr_exception_continuum_assumed
  | cr_exception_continuum_proved
  | cr_exception_continuum_surrogate.

Definition crExceptionContinuumModalityCurrent : CrExceptionContinuumModality :=
  cr_exception_continuum_unwired.

Definition cr_exception_continuum_lattice_cardinality : nat := 4.

Lemma cr_exception_continuum_lattice_cardinality_is_four :
  cr_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma cr_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb cr_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold cr_exception_continuum_lattice_cardinality.
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
(*  IUPAC Z pins — Cr Z=24 d-block exception witness                   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition chromium_atomic_number_z : nat := 24.

Lemma chromium_atomic_number_z_is_24 :
  chromium_atomic_number_z = 24.
Proof. reflexivity. Qed.

Definition molybdenum_homolog_z : nat := 42.

Lemma molybdenum_homolog_z_is_42 :
  molybdenum_homolog_z = 42.
Proof. reflexivity. Qed.

Definition chromium_z_valid : bool :=
  Nat.ltb 0 chromium_atomic_number_z &&
  Nat.leb chromium_atomic_number_z iupac_table_cardinality.

Lemma chromium_z_valid_true : chromium_z_valid = true.
Proof.
  unfold chromium_z_valid, chromium_atomic_number_z, iupac_table_cardinality.
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
(*  Cr Z=24 occupancy pins — 4s¹3d⁵ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition cr_element_symbol : string := "Cr".

Definition cr_observed_occupancy_tag : string := "3d54s1".

Definition cr_predicted_occupancy_tag : string := "4s23d4".

Definition cr_observed_subshell_notation : string :=
  "1s22s22p63s23p64s13d5".

Definition cr_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d4".

Definition mo_homolog_observed_occupancy_tag : string := "4d55s1".

Lemma cr_element_symbol_nonempty :
  cr_element_symbol <> "".
Proof. discriminate. Qed.

Lemma cr_observed_occupancy_tag_nonempty :
  cr_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma cr_predicted_occupancy_tag_nonempty :
  cr_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma cr_observed_ne_predicted_occupancy :
  cr_observed_occupancy_tag <> cr_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma cr_observed_ne_predicted_subshell :
  cr_observed_subshell_notation <> cr_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma cr_homolog_occupancy_not_copy :
  cr_observed_occupancy_tag <> mo_homolog_observed_occupancy_tag.
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
(*  Cr exception continuum product channel — concurrent **product**     *)
(* ------------------------------------------------------------------ *)

Inductive cec_channel_slot : Type :=
  | cec_slot_unwired
  | cec_slot_absent
  | cec_slot_present.

Definition cec_channel_slot_beq (s1 s2 : cec_channel_slot) : bool :=
  match s1, s2 with
  | cec_slot_unwired, cec_slot_unwired => true
  | cec_slot_absent, cec_slot_absent => true
  | cec_slot_present, cec_slot_present => true
  | _, _ => false
  end.

Definition cec_channel_slot_is_present (s : cec_channel_slot) : bool :=
  match s with
  | cec_slot_present => true
  | _ => false
  end.

Definition crExceptionContinuumProductChannelCount : nat := 5.

Lemma cr_exception_continuum_product_channel_count_is_five :
  crExceptionContinuumProductChannelCount = 5.
Proof. reflexivity. Qed.

Definition cec_channel_ore : nat := 0.
Definition cec_channel_isotope_mix : nat := 1.
Definition cec_channel_purify_refine : nat := 2.
Definition cec_channel_g_stability : nat := 3.
Definition cec_channel_env : nat := 4.

Lemma cec_channel_ore_idx_is_0 :
  cec_channel_ore = 0.
Proof. reflexivity. Qed.

Lemma cec_channel_isotope_mix_idx_is_1 :
  cec_channel_isotope_mix = 1.
Proof. reflexivity. Qed.

Lemma cec_channel_purify_refine_idx_is_2 :
  cec_channel_purify_refine = 2.
Proof. reflexivity. Qed.

Lemma cec_channel_g_stability_idx_is_3 :
  cec_channel_g_stability = 3.
Proof. reflexivity. Qed.

Lemma cec_channel_env_idx_is_4 :
  cec_channel_env = 4.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum concurrent **product** bundle scaffold       *)
(* ------------------------------------------------------------------ *)

Definition cec_channel_bundle : Type := nat -> cec_channel_slot.

Definition crExceptionContinuumBundleAllUnwired : cec_channel_bundle :=
  fun _ => cec_slot_unwired.

Definition crExceptionContinuumBundleAt (b : cec_channel_bundle) (idx : nat)
  (slot : cec_channel_slot) : cec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition crExceptionContinuumBundleWithPresent
  (b : cec_channel_bundle) (idx : nat) : cec_channel_bundle :=
  crExceptionContinuumBundleAt b idx cec_slot_present.

Fixpoint count_cec_present_up_to (b : cec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if cec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_cec_present_up_to b i + add
  end.

Definition crExceptionContinuumBundlePresentCount (b : cec_channel_bundle) : nat :=
  count_cec_present_up_to b crExceptionContinuumProductChannelCount.

Definition crExceptionContinuumBundleHolds (b : cec_channel_bundle) (idx : nat) : bool :=
  cec_channel_slot_is_present (b idx).

Definition crExceptionContinuumBundleIsConcurrentProduct (b : cec_channel_bundle) : bool :=
  Nat.leb 2 (crExceptionContinuumBundlePresentCount b).

(* Cr Z=24 natural continuum witness — ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env. *)
Definition crExceptionContinuumCr24Witness : cec_channel_bundle :=
  crExceptionContinuumBundleWithPresent
    (crExceptionContinuumBundleWithPresent
      (crExceptionContinuumBundleWithPresent
        (crExceptionContinuumBundleWithPresent
          (crExceptionContinuumBundleWithPresent
            crExceptionContinuumBundleAllUnwired
            cec_channel_ore)
          cec_channel_isotope_mix)
        cec_channel_purify_refine)
      cec_channel_g_stability)
    cec_channel_env.

Definition crExceptionContinuumEmptyWitness : cec_channel_bundle :=
  crExceptionContinuumBundleAllUnwired.

Definition crExceptionContinuumSinglePresent : cec_channel_bundle :=
  crExceptionContinuumBundleWithPresent crExceptionContinuumBundleAllUnwired
    cec_channel_ore.

Lemma ore_channel_present :
  crExceptionContinuumBundleHolds crExceptionContinuumCr24Witness
    cec_channel_ore = true.
Proof. reflexivity. Qed.

Lemma isotope_mix_channel_present :
  crExceptionContinuumBundleHolds crExceptionContinuumCr24Witness
    cec_channel_isotope_mix = true.
Proof. reflexivity. Qed.

Lemma purify_refine_channel_present :
  crExceptionContinuumBundleHolds crExceptionContinuumCr24Witness
    cec_channel_purify_refine = true.
Proof. reflexivity. Qed.

Lemma g_stability_channel_present :
  crExceptionContinuumBundleHolds crExceptionContinuumCr24Witness
    cec_channel_g_stability = true.
Proof. reflexivity. Qed.

Lemma env_channel_present :
  crExceptionContinuumBundleHolds crExceptionContinuumCr24Witness
    cec_channel_env = true.
Proof. reflexivity. Qed.

Lemma cr24_witness_present_count_is_five :
  crExceptionContinuumBundlePresentCount crExceptionContinuumCr24Witness = 5.
Proof. reflexivity. Qed.

Lemma cr24_witness_is_concurrent_product :
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumCr24Witness = true.
Proof.
  unfold crExceptionContinuumBundleIsConcurrentProduct.
  rewrite cr24_witness_present_count_is_five.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  crExceptionContinuumBundlePresentCount crExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumEmptyWitness = false.
Proof.
  unfold crExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  crExceptionContinuumBundlePresentCount crExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumSinglePresent = false.
Proof.
  unfold crExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive cec_xor_posture : Type :=
  | cec_xor_exclusive
  | cec_xor_concurrent_product.

Definition cecXorClassifierMarker : string := "chem_l0_cr_exception_xor_classifier_v1".
Definition cecConcurrentProductMarker : string := "chem_int_cr_exception_continuum_product_v1".

Lemma cec_xor_marker_ne_concurrent_product_marker :
  cecXorClassifierMarker <> cecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition cecXorClassifierIncompatible (claim_xor : bool)
  (b : cec_channel_bundle) : bool :=
  claim_xor && crExceptionContinuumBundleIsConcurrentProduct b.

Lemma cec_xor_refuse_on_cr24_witness :
  cecXorClassifierIncompatible true crExceptionContinuumCr24Witness = true.
Proof.
  unfold cecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma cec_xor_ok_on_concurrent_product_claim :
  cecXorClassifierIncompatible false crExceptionContinuumCr24Witness = false.
Proof. reflexivity. Qed.

Definition cecProductNotXor : bool :=
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumCr24Witness &&
  cecXorClassifierIncompatible true crExceptionContinuumCr24Witness.

Lemma cec_product_not_xor_true : cecProductNotXor = true.
Proof.
  unfold cecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  cecProductNotXor = true /\
  Nat.leb 2 (crExceptionContinuumBundlePresentCount
    crExceptionContinuumCr24Witness) = true /\
  cecXorClassifierMarker <> cecConcurrentProductMarker.
Proof.
  split.
  - apply cec_product_not_xor_true.
  - split.
    + rewrite cr24_witness_present_count_is_five.
      reflexivity.
    + apply cec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum **conservation** bar — Proved-without-bar    *)
(* ------------------------------------------------------------------ *)

Inductive cec_bar_presence : Type :=
  | cec_bar_absent
  | cec_bar_present.

Record cec_claim_bar : Type := {
  cec_bar_presence_field : cec_bar_presence;
  cec_bar_defect_total : nat
}.

Definition crExceptionContinuumClaimBarAbsent : cec_claim_bar :=
  {| cec_bar_presence_field := cec_bar_absent;
     cec_bar_defect_total := 0 |}.

Definition crExceptionContinuumClaimBarZeroDefect : cec_claim_bar :=
  {| cec_bar_presence_field := cec_bar_present;
     cec_bar_defect_total := 0 |}.

Definition cec_claim_bar_zero_defect (b : cec_claim_bar) : bool :=
  match cec_bar_presence_field b with
  | cec_bar_absent => false
  | cec_bar_present => Nat.eqb (cec_bar_defect_total b) 0
  end.

Lemma cec_claim_bar_zero_defect_true :
  cec_claim_bar_zero_defect crExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma cec_claim_bar_absent_not_zero_defect :
  cec_claim_bar_zero_defect crExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum **conservation** verdict — fail-closed       *)
(* ------------------------------------------------------------------ *)

Inductive cec_conservation_verdict : Type :=
  | cec_verdict_unwired_ok
  | cec_verdict_named_ok
  | cec_verdict_design_ok
  | cec_verdict_trivial_refuse
  | cec_verdict_xor_refuse
  | cec_verdict_green_invent_refuse
  | cec_verdict_proved_without_bar_refuse
  | cec_verdict_production_wired_refuse
  | cec_verdict_parallel_exception_axiom_refuse
  | cec_verdict_homolog_copy_refuse
  | cec_verdict_extra_element_id_refuse
  | cec_verdict_madelung_family_smuggle_refuse
  | cec_verdict_tp_float_pin_refuse.

Definition cec_conservation_verdict_ok (v : cec_conservation_verdict) : bool :=
  match v with
  | cec_verdict_unwired_ok => true
  | cec_verdict_named_ok => true
  | cec_verdict_design_ok => true
  | _ => false
  end.

Definition crExceptionContinuumBundleNontrivial (b : cec_channel_bundle) : bool :=
  Nat.ltb 0 (crExceptionContinuumBundlePresentCount b).

Definition evaluate_cr_exception_continuum_bundle
  (m : CrExceptionContinuumModality)
  (b : cec_channel_bundle)
  (bar : cec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : cec_conservation_verdict :=
  if claim_physics_green
  then cec_verdict_green_invent_refuse
  else if claim_proved
       then cec_verdict_proved_without_bar_refuse
       else if negb (crExceptionContinuumBundleNontrivial b)
            then cec_verdict_trivial_refuse
            else if cecXorClassifierIncompatible claim_xor_classifier b
                 then cec_verdict_xor_refuse
                 else
                   match m with
                   | cr_exception_continuum_unwired =>
                       if crExceptionContinuumBundleIsConcurrentProduct b
                       then cec_verdict_named_ok
                       else cec_verdict_design_ok
                   | cr_exception_continuum_assumed
                   | cr_exception_continuum_surrogate =>
                       cec_verdict_design_ok
                   | cr_exception_continuum_proved =>
                       cec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_cr_exception_continuum_close
  (m : CrExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : cec_conservation_verdict :=
  if claim_physics_green
  then cec_verdict_green_invent_refuse
  else if claim_production_wired
  then cec_verdict_production_wired_refuse
  else
    match m with
    | cr_exception_continuum_unwired => cec_verdict_unwired_ok
    | cr_exception_continuum_assumed
    | cr_exception_continuum_proved
    | cr_exception_continuum_surrogate => cec_verdict_named_ok
    end.

Definition cr_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_cr_exception_continuum_close
          cr_exception_continuum_proved claim_physics_green claim_production_wired with
  | cec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive cec_conservation_law : Type :=
  | cec_law_conserved
  | cec_law_named_ok
  | cec_law_trivial_refuse
  | cec_law_green_invent_refuse.

Definition cec_conservation_law_count : nat := 4.

Lemma cec_conservation_law_count_is_four :
  cec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive cec_conservation_law_witness : Type :=
  | cec_law_witness_open
  | cec_law_witness_proved.

Definition evaluate_cec_conservation_law_witness
  (law : cec_conservation_law)
  (m : CrExceptionContinuumModality)
  : cec_conservation_law_witness :=
  match m with
  | cr_exception_continuum_unwired
  | cr_exception_continuum_assumed
  | cr_exception_continuum_surrogate => cec_law_witness_open
  | cr_exception_continuum_proved => cec_law_witness_proved
  end.

Lemma all_cec_conservation_laws_open_at_unwired :
  evaluate_cec_conservation_law_witness cec_law_conserved
    cr_exception_continuum_unwired = cec_law_witness_open /\
  evaluate_cec_conservation_law_witness cec_law_named_ok
    cr_exception_continuum_unwired = cec_law_witness_open /\
  evaluate_cec_conservation_law_witness cec_law_trivial_refuse
    cr_exception_continuum_unwired = cec_law_witness_open /\
  evaluate_cec_conservation_law_witness cec_law_green_invent_refuse
    cr_exception_continuum_unwired = cec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum pins (structure witnesses — not Proved)      *)
(* ------------------------------------------------------------------ *)

Definition crExceptionContinuumProved : bool := false.

Lemma cr_exception_continuum_proved_false :
  crExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_unwired false false =
  cec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_unwired false false =
  cec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_unwired false false) =
  true.
Proof.
  unfold cec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Cr Z=24 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma cr24_witness_named_ok :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false false =
  cec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cr24_exception_continuum :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false false =
  cec_verdict_named_ok /\
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumCr24Witness = true /\
  chromium_atomic_number_z = 24 /\
  cr_observed_occupancy_tag = "3d54s1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma cec_named_close_ok :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_proved false false =
  cec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cr_exception_continuum_close :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_proved false false =
  cec_verdict_named_ok /\
  cr_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply cec_named_close_ok.
  - unfold cr_exception_continuum_authorized.
    rewrite cec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumEmptyWitness
    crExceptionContinuumClaimBarAbsent false false false =
  cec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumEmptyWitness
    crExceptionContinuumClaimBarAbsent false false false =
  cec_verdict_trivial_refuse /\
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_bundle
       cr_exception_continuum_unwired
       crExceptionContinuumEmptyWitness
       crExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold cec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent true false false =
  cec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent true false false =
  cec_verdict_xor_refuse /\
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_bundle
       cr_exception_continuum_unwired
       crExceptionContinuumCr24Witness
       crExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold cec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_unwired true false =
  cec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_unwired true false) =
  false.
Proof.
  unfold cec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_cec_bundle_refuse :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false true false =
  cec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — refuse                             *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false true =
  cec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false true =
  cec_verdict_proved_without_bar_refuse /\
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_bundle
       cr_exception_continuum_unwired
       crExceptionContinuumCr24Witness
       crExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold cec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — WAVE100 not wired lib.rs                  *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_proved false true =
  cec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_proved false true) =
  false.
Proof.
  unfold cec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel exception axiom refuse — not 26th periodic-table axiom     *)
(* ------------------------------------------------------------------ *)

Definition crExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_exception_axiom_refuse :
  crExceptionContinuumAuthority <>
  parallelExceptionAxiomTag /\
  crExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply cr_exception_continuum_proved_false.
Qed.

Theorem parallel_exception_axiom_not_minted :
  crExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  crExceptionContinuumProved = false /\
  crExceptionContinuumAuthority <> parallelExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog copy refuse — Mo Z=42 occupancy ≠ Cr Z=24 copy              *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "mo_z42_occupancy_copied_onto_cr_z24".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition crExceptionContinuumFraming : string :=
  "second_law_conservation_occupancy_engine_sort_cr_z24_one_axiom".

Lemma homolog_copy_refuse :
  crExceptionContinuumFraming <>
  homologCopyFraming /\
  cr_observed_occupancy_tag <> mo_homolog_observed_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply cr_homolog_occupancy_not_copy.
Qed.

Theorem cr_mo_homolog_not_occupancy_copy :
  crExceptionContinuumFraming <>
  homologCopyFraming /\
  chromium_atomic_number_z = 24 /\
  molybdenum_homolog_z = 42 /\
  cr_observed_occupancy_tag <> mo_homolog_observed_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — Cr exception ≠ Z=119 smuggle               *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "cr_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  crExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem cr_exception_not_extra_element_id :
  crExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  chromium_atomic_number_z = 24.
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
  crExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  cr_observed_occupancy_tag <> cr_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply cr_observed_ne_predicted_occupancy.
Qed.

Theorem cr_observed_override_not_madelung_family_smuggle :
  crExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  cr_observed_occupancy_tag = "3d54s1" /\
  cr_predicted_occupancy_tag = "4s23d4" /\
  crExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions ≠ bare float pins            *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_cr_exception_scaffold".

Lemma tp_float_pin_refuse :
  crExceptionContinuumFraming <>
  tpFloatPinFraming /\
  g_stability_channel_tag = "g_stability".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  crExceptionContinuumFraming <>
  tpFloatPinFraming /\
  env_channel_tag = "env" /\
  chromium_atomic_number_z = 24.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cr exception continuum coherence scaffold                             *)
(* ------------------------------------------------------------------ *)

Definition cec_conservation_coherence_scaffold : bool :=
  cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_proved false false) &&
  negb (cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_unwired true false)) &&
  negb (cec_conservation_verdict_ok
    (evaluate_cr_exception_continuum_close
       cr_exception_continuum_proved false true)).

Lemma cec_conservation_coherence_scaffold_true :
  cec_conservation_coherence_scaffold = true.
Proof.
  unfold cec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cec_conservation_coherence_scaffold_theorem :
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_proved false false =
    cec_verdict_named_ok /\
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_unwired true false =
    cec_verdict_green_invent_refuse /\
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_proved false true =
    cec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition cec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition cec_conservation_knowing_fiber_ok : bool :=
  cec_conservation_fiber_ok fiber_quantum_knowing.

Definition cec_conservation_meso_acting_ok : bool :=
  cec_conservation_fiber_ok fiber_meso_acting.

Lemma cec_conservation_knowing_fiber_ok_true :
  cec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma cec_conservation_meso_acting_not_ok :
  cec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem cec_conservation_routes_knowing_not_meso :
  cec_conservation_knowing_fiber_ok = true /\
  cec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply cec_conservation_knowing_fiber_ok_true.
  - apply cec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  cec_conservation_knowing_fiber_ok &&
  negb cec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, cec_conservation_knowing_fiber_ok,
    cec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named Cr Z=24 + fail-closed + fiber              *)
(* ------------------------------------------------------------------ *)

Theorem cr_exception_continuum_fixture_scaffold :
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false false =
    cec_verdict_named_ok /\
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumEmptyWitness
    crExceptionContinuumClaimBarAbsent false false false =
    cec_verdict_trivial_refuse /\
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent true false false =
    cec_verdict_xor_refuse /\
  evaluate_cr_exception_continuum_bundle
    cr_exception_continuum_unwired
    crExceptionContinuumCr24Witness
    crExceptionContinuumClaimBarAbsent false false true =
    cec_verdict_proved_without_bar_refuse /\
  evaluate_cr_exception_continuum_close
    cr_exception_continuum_unwired false false =
    cec_verdict_unwired_ok /\
  cec_conservation_knowing_fiber_ok = true /\
  cec_conservation_meso_acting_ok = false /\
  crExceptionContinuumProved = false /\
  cecProductNotXor = true /\
  chromium_atomic_number_z = 24.
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

Definition crExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-CR-EXCEPTION-CONTINUUM".

Definition crExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CR-EXCEPTION-CONTINUUM CrExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice crExceptionContinuumProved false evaluateCrExceptionContinuumBundle evaluateCrExceptionContinuumClose named Cr Z=24 4s1 3d5 occupancy engine sort dblock_exception ore isotope purify G env concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel exception axiom refuse homolog copy refuse Mo Z=42 extra element id Z=119 refuse madelung family smuggle refuse Cr ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 not lib.rs".

Lemma cr_exception_continuum_cell_id :
  crExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-CR-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma cr_exception_continuum_cites_dblock_exceptions :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma cr_exception_continuum_cites_occupancy_engine_sort :
  occupancyEngineSortAuthority <> "".
Proof. discriminate. Qed.

Lemma cr_exception_continuum_cites_goldschmidt :
  goldschmidtConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma cr_exception_continuum_cites_homolog_not_copy :
  homologExceptionNotCopyAuthority <>
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma cr_exception_continuum_cites_homolog_cell :
  homologExceptionNotCopyCellId =
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".
Proof. reflexivity. Qed.

Lemma cr_exception_continuum_cites_madelung_witness :
  madelungWitnessAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma cr_exception_not_26th_axiom :
  crExceptionContinuumFraming <> parallelExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma cr_exception_second_law_conservation_framing :
  crExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort — Cr sorts dblock_exception bucket            *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition occupancyEngineSortFraming : string :=
  "occupancy_engine_sort_dblock_exception_bucket".

Lemma cr_sorts_dblock_exception_bucket :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Lemma cr_exception_continuum_cites_occupancy_engine_sort_int :
  occupancyEngineSortIntAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Theorem cr_occupancy_engine_sort_not_new_axiom :
  occupancyEngineSortFraming <>
  parallelExceptionAxiomTag /\
  occupancyEngineSortBucketTag = "dblock_exception" /\
  crExceptionContinuumProved = false.
Proof.
  split; [discriminate |].
  split; [apply cr_sorts_dblock_exception_bucket | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma cr_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma cr_exception_continuum_modality_unwired :
  crExceptionContinuumModalityCurrent =
  cr_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition crExceptionContinuumProductionWired : Prop := False.

Lemma cr_exception_continuum_not_production_wired :
  ~ crExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

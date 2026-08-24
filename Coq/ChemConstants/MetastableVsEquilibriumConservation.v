(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* metastablevsequilibriumconservation *)
(* metastable_vs_equilibrium *)
(* chem_formal_q_coq_metastable_vs_equilibrium_conservation *)

(* ================================================================== *)
(*  UMST-Formal: MetastableVsEquilibriumConservation.v                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 12 **metastable_vs_equilibrium**            *)
(*  **conservation**. Metastable vs equilibrium is a concurrent         *)
(*  PatternBundle Π_c factor — **product** not XOR. Fast kinetics is    *)
(*  not the equilibrium G hull; time is a named remainder on SCALE-02,  *)
(*  not a new law. metastableVsEquilibriumConservationProved false.     *)
(*  Modality Unwired. PatternProductConservation.v sibling.             *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs     *)
(*  INT: umst/umst-chem/src/metastable_equilibrium.rs (read-only cite). *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-12 **metastable_vs_equilibrium** **conservation** modality    *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive MetastableVsEquilibriumConservationModality : Type :=
  | metastable_vs_equilibrium_conservation_unwired
  | metastable_vs_equilibrium_conservation_assumed
  | metastable_vs_equilibrium_conservation_proved
  | metastable_vs_equilibrium_conservation_surrogate.

Definition metastableVsEquilibriumConservationModalityCurrent :
  MetastableVsEquilibriumConservationModality :=
  metastable_vs_equilibrium_conservation_unwired.

Definition metastable_vs_equilibrium_lattice_cardinality : nat := 4.

Lemma metastable_vs_equilibrium_lattice_cardinality_is_four :
  metastable_vs_equilibrium_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_lattice_not_118_squared :
  negb (Nat.eqb metastable_vs_equilibrium_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold metastable_vs_equilibrium_lattice_cardinality.
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

(* North-star §2 class 12 — metastable_vs_equilibrium concurrent Π_c factor. *)
Definition pattern_class_metastable_vs_equilibrium_idx : nat := 12.

Lemma pattern_class_metastable_vs_equilibrium_idx_is_12 :
  pattern_class_metastable_vs_equilibrium_idx = 12.
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_class_index_valid :
  pattern_class_index_valid pattern_class_metastable_vs_equilibrium_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_metastable_vs_equilibrium_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierMetastableVsEquilibriumRowId : string := "X12".

Lemma cross_classifier_metastable_vs_equilibrium_row_named :
  crossClassifierMetastableVsEquilibriumRowId = "X12".
Proof. reflexivity. Qed.

Definition pattern_class_metastable_vs_equilibrium_tag : string :=
  "metastable_vs_equilibrium".

Definition north_star_class_12_metastable_tag : string :=
  "class 12 metastable".

Lemma pattern_class_metastable_vs_equilibrium_tag_nonempty :
  pattern_class_metastable_vs_equilibrium_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_12_metastable_tag_nonempty :
  north_star_class_12_metastable_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — C Z=6 diamond/graphite metastable witness           *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition carbon_atomic_number_z : nat := 6.

Lemma carbon_atomic_number_z_is_6 :
  carbon_atomic_number_z = 6.
Proof. reflexivity. Qed.

Definition carbon_z_valid : bool :=
  Nat.ltb 0 carbon_atomic_number_z &&
  Nat.leb carbon_atomic_number_z iupac_table_cardinality.

Lemma carbon_z_valid_true : carbon_z_valid = true.
Proof.
  unfold carbon_z_valid, carbon_atomic_number_z, iupac_table_cardinality.
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

Definition metastable_vs_equilibrium_factor_tag : string :=
  "metastable_vs_equilibrium".

Definition equilibrium_basin_channel_tag : string := "equilibrium_basin".

Definition metastable_trap_channel_tag : string := "metastable_trap".

Definition reaction_kinetics_remainder_tag : string := "reaction_kinetics".

Lemma metastable_vs_equilibrium_factor_tag_nonempty :
  metastable_vs_equilibrium_factor_tag <> "".
Proof. discriminate. Qed.

Lemma equilibrium_basin_channel_tag_nonempty :
  equilibrium_basin_channel_tag <> "".
Proof. discriminate. Qed.

Lemma metastable_trap_channel_tag_nonempty :
  metastable_trap_channel_tag <> "".
Proof. discriminate. Qed.

Lemma reaction_kinetics_remainder_tag_nonempty :
  reaction_kinetics_remainder_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium product channel — concurrent **product**   *)
(* ------------------------------------------------------------------ *)

Inductive mve_channel_slot : Type :=
  | mve_slot_unwired
  | mve_slot_absent
  | mve_slot_present.

Definition mve_channel_slot_beq (s1 s2 : mve_channel_slot) : bool :=
  match s1, s2 with
  | mve_slot_unwired, mve_slot_unwired => true
  | mve_slot_absent, mve_slot_absent => true
  | mve_slot_present, mve_slot_present => true
  | _, _ => false
  end.

Definition mve_channel_slot_is_present (s : mve_channel_slot) : bool :=
  match s with
  | mve_slot_present => true
  | _ => false
  end.

Definition metastableVsEquilibriumProductChannelCount : nat := 3.

Lemma metastable_vs_equilibrium_product_channel_count_is_three :
  metastableVsEquilibriumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = equilibrium G hull, 1 = metastable trap, 2 = class 12. *)
Definition mve_channel_equilibrium_basin : nat := 0.
Definition mve_channel_metastable_trap : nat := 1.
Definition mve_channel_class12_metastable_vs_equilibrium : nat := 2.

Lemma mve_channel_equilibrium_basin_idx_is_0 :
  mve_channel_equilibrium_basin = 0.
Proof. reflexivity. Qed.

Lemma mve_channel_metastable_trap_idx_is_1 :
  mve_channel_metastable_trap = 1.
Proof. reflexivity. Qed.

Lemma mve_channel_class12_metastable_vs_equilibrium_idx_is_2 :
  mve_channel_class12_metastable_vs_equilibrium = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium concurrent **product** bundle scaffold     *)
(* ------------------------------------------------------------------ *)

Definition mve_channel_bundle : Type := nat -> mve_channel_slot.

Definition metastableVsEquilibriumBundleAllUnwired : mve_channel_bundle :=
  fun _ => mve_slot_unwired.

Definition metastableVsEquilibriumBundleAt (b : mve_channel_bundle) (idx : nat)
  (slot : mve_channel_slot) : mve_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition metastableVsEquilibriumBundleWithPresent
  (b : mve_channel_bundle) (idx : nat) : mve_channel_bundle :=
  metastableVsEquilibriumBundleAt b idx mve_slot_present.

Fixpoint count_mve_present_up_to (b : mve_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if mve_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_mve_present_up_to b i + add
  end.

Definition metastableVsEquilibriumBundlePresentCount (b : mve_channel_bundle) : nat :=
  count_mve_present_up_to b metastableVsEquilibriumProductChannelCount.

Definition metastableVsEquilibriumBundleHolds (b : mve_channel_bundle) (idx : nat) : bool :=
  mve_channel_slot_is_present (b idx).

Definition metastableVsEquilibriumBundleIsConcurrentProduct (b : mve_channel_bundle) : bool :=
  Nat.leb 2 (metastableVsEquilibriumBundlePresentCount b).

(* C Z=6 equilibrium basin + metastable trap + class-12 concurrent witness. *)
Definition metastableVsEquilibriumC6Witness : mve_channel_bundle :=
  metastableVsEquilibriumBundleWithPresent
    (metastableVsEquilibriumBundleWithPresent
      (metastableVsEquilibriumBundleWithPresent metastableVsEquilibriumBundleAllUnwired
        mve_channel_equilibrium_basin)
      mve_channel_metastable_trap)
    mve_channel_class12_metastable_vs_equilibrium.

Definition metastableVsEquilibriumEmptyWitness : mve_channel_bundle :=
  metastableVsEquilibriumBundleAllUnwired.

Definition metastableVsEquilibriumSinglePresent : mve_channel_bundle :=
  metastableVsEquilibriumBundleWithPresent metastableVsEquilibriumBundleAllUnwired
    mve_channel_equilibrium_basin.

Lemma equilibrium_basin_channel_present :
  metastableVsEquilibriumBundleHolds metastableVsEquilibriumC6Witness
    mve_channel_equilibrium_basin = true.
Proof. reflexivity. Qed.

Lemma metastable_trap_channel_present :
  metastableVsEquilibriumBundleHolds metastableVsEquilibriumC6Witness
    mve_channel_metastable_trap = true.
Proof. reflexivity. Qed.

Lemma class12_metastable_vs_equilibrium_channel_present :
  metastableVsEquilibriumBundleHolds metastableVsEquilibriumC6Witness
    mve_channel_class12_metastable_vs_equilibrium = true.
Proof. reflexivity. Qed.

Lemma c6_witness_present_count_is_three :
  metastableVsEquilibriumBundlePresentCount metastableVsEquilibriumC6Witness = 3.
Proof. reflexivity. Qed.

Lemma c6_witness_is_concurrent_product :
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumC6Witness = true.
Proof.
  unfold metastableVsEquilibriumBundleIsConcurrentProduct.
  rewrite c6_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  metastableVsEquilibriumBundlePresentCount metastableVsEquilibriumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumEmptyWitness = false.
Proof.
  unfold metastableVsEquilibriumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  metastableVsEquilibriumBundlePresentCount metastableVsEquilibriumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumSinglePresent = false.
Proof.
  unfold metastableVsEquilibriumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive mve_xor_posture : Type :=
  | mve_xor_exclusive
  | mve_xor_concurrent_product.

Definition mveXorClassifierMarker : string := "chem_l0_metastable_vs_equilibrium_xor_classifier_v1".
Definition mveConcurrentProductMarker : string := "chem_int_metastable_vs_equilibrium_product_v1".

Lemma mve_xor_marker_ne_concurrent_product_marker :
  mveXorClassifierMarker <> mveConcurrentProductMarker.
Proof. discriminate. Qed.

Definition mveXorClassifierIncompatible (claim_xor : bool)
  (b : mve_channel_bundle) : bool :=
  claim_xor && metastableVsEquilibriumBundleIsConcurrentProduct b.

Lemma mve_xor_refuse_on_c6_witness :
  mveXorClassifierIncompatible true metastableVsEquilibriumC6Witness = true.
Proof.
  unfold mveXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma mve_xor_ok_on_concurrent_product_claim :
  mveXorClassifierIncompatible false metastableVsEquilibriumC6Witness = false.
Proof. reflexivity. Qed.

Definition mveProductNotXor : bool :=
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumC6Witness &&
  mveXorClassifierIncompatible true metastableVsEquilibriumC6Witness.

Lemma mve_product_not_xor_true : mveProductNotXor = true.
Proof.
  unfold mveProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  mveProductNotXor = true /\
  Nat.leb 2 (metastableVsEquilibriumBundlePresentCount
    metastableVsEquilibriumC6Witness) = true /\
  mveXorClassifierMarker <> mveConcurrentProductMarker.
Proof.
  split.
  - apply mve_product_not_xor_true.
  - split.
    + rewrite c6_witness_present_count_is_three.
      reflexivity.
    + apply mve_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium **conservation** bar — Proved-without-bar *)
(* ------------------------------------------------------------------ *)

Inductive mve_bar_presence : Type :=
  | mve_bar_absent
  | mve_bar_present.

Record mve_claim_bar : Type := {
  mve_bar_presence_field : mve_bar_presence;
  mve_bar_defect_total : nat
}.

Definition metastableVsEquilibriumClaimBarAbsent : mve_claim_bar :=
  {| mve_bar_presence_field := mve_bar_absent;
     mve_bar_defect_total := 0 |}.

Definition metastableVsEquilibriumClaimBarZeroDefect : mve_claim_bar :=
  {| mve_bar_presence_field := mve_bar_present;
     mve_bar_defect_total := 0 |}.

Definition mve_claim_bar_zero_defect (b : mve_claim_bar) : bool :=
  match mve_bar_presence_field b with
  | mve_bar_absent => false
  | mve_bar_present => Nat.eqb (mve_bar_defect_total b) 0
  end.

Lemma mve_claim_bar_zero_defect_true :
  mve_claim_bar_zero_defect metastableVsEquilibriumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma mve_claim_bar_absent_not_zero_defect :
  mve_claim_bar_zero_defect metastableVsEquilibriumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium **conservation** verdict — fail-closed    *)
(* ------------------------------------------------------------------ *)

Inductive mve_conservation_verdict : Type :=
  | mve_verdict_unwired_ok
  | mve_verdict_named_ok
  | mve_verdict_design_ok
  | mve_verdict_trivial_refuse
  | mve_verdict_xor_refuse
  | mve_verdict_green_invent_refuse
  | mve_verdict_proved_without_bar_refuse
  | mve_verdict_production_wired_refuse
  | mve_verdict_parallel_metastability_axiom_refuse
  | mve_verdict_species_id_smuggle_refuse
  | mve_verdict_extra_element_id_refuse
  | mve_verdict_fast_kinetics_not_equilibrium_g_hull_refuse
  | mve_verdict_time_remainder_not_new_law_refuse
  | mve_verdict_tp_float_pin_refuse.

Definition mve_conservation_verdict_ok (v : mve_conservation_verdict) : bool :=
  match v with
  | mve_verdict_unwired_ok => true
  | mve_verdict_named_ok => true
  | mve_verdict_design_ok => true
  | _ => false
  end.

Definition metastableVsEquilibriumBundleNontrivial (b : mve_channel_bundle) : bool :=
  Nat.ltb 0 (metastableVsEquilibriumBundlePresentCount b).

Definition evaluate_metastable_vs_equilibrium_bundle
  (m : MetastableVsEquilibriumConservationModality)
  (b : mve_channel_bundle)
  (bar : mve_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_fast_kinetics_as_equilibrium_g_hull : bool)
  (claim_time_as_new_law : bool) : mve_conservation_verdict :=
  if claim_physics_green
  then mve_verdict_green_invent_refuse
  else if claim_fast_kinetics_as_equilibrium_g_hull
       then mve_verdict_fast_kinetics_not_equilibrium_g_hull_refuse
       else if claim_time_as_new_law
            then mve_verdict_time_remainder_not_new_law_refuse
            else if claim_proved
                 then mve_verdict_proved_without_bar_refuse
                 else if negb (metastableVsEquilibriumBundleNontrivial b)
                      then mve_verdict_trivial_refuse
                      else if mveXorClassifierIncompatible claim_xor_classifier b
                           then mve_verdict_xor_refuse
                           else
                             match m with
                             | metastable_vs_equilibrium_conservation_unwired =>
                                 if metastableVsEquilibriumBundleIsConcurrentProduct b
                                 then mve_verdict_named_ok
                                 else mve_verdict_design_ok
                             | metastable_vs_equilibrium_conservation_assumed
                             | metastable_vs_equilibrium_conservation_surrogate =>
                                 mve_verdict_design_ok
                             | metastable_vs_equilibrium_conservation_proved =>
                                 mve_verdict_proved_without_bar_refuse
                             end.

Definition evaluate_metastable_vs_equilibrium_conservation_close
  (m : MetastableVsEquilibriumConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : mve_conservation_verdict :=
  if claim_physics_green
  then mve_verdict_green_invent_refuse
  else if claim_production_wired
  then mve_verdict_production_wired_refuse
  else
    match m with
    | metastable_vs_equilibrium_conservation_unwired => mve_verdict_unwired_ok
    | metastable_vs_equilibrium_conservation_assumed
    | metastable_vs_equilibrium_conservation_proved
    | metastable_vs_equilibrium_conservation_surrogate => mve_verdict_named_ok
    end.

Definition metastable_vs_equilibrium_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_metastable_vs_equilibrium_conservation_close
          metastable_vs_equilibrium_conservation_proved claim_physics_green claim_production_wired with
  | mve_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium **conservation** law cells — four laws    *)
(* ------------------------------------------------------------------ *)

Inductive mve_conservation_law : Type :=
  | mve_law_conserved
  | mve_law_named_ok
  | mve_law_trivial_refuse
  | mve_law_green_invent_refuse.

Definition mve_conservation_law_count : nat := 4.

Lemma mve_conservation_law_count_is_four :
  mve_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive mve_conservation_law_witness : Type :=
  | mve_law_witness_open
  | mve_law_witness_proved.

Definition evaluate_mve_conservation_law_witness
  (law : mve_conservation_law)
  (m : MetastableVsEquilibriumConservationModality)
  : mve_conservation_law_witness :=
  match m with
  | metastable_vs_equilibrium_conservation_unwired
  | metastable_vs_equilibrium_conservation_assumed
  | metastable_vs_equilibrium_conservation_surrogate => mve_law_witness_open
  | metastable_vs_equilibrium_conservation_proved => mve_law_witness_proved
  end.

Lemma all_mve_conservation_laws_open_at_unwired :
  evaluate_mve_conservation_law_witness mve_law_conserved
    metastable_vs_equilibrium_conservation_unwired = mve_law_witness_open /\
  evaluate_mve_conservation_law_witness mve_law_named_ok
    metastable_vs_equilibrium_conservation_unwired = mve_law_witness_open /\
  evaluate_mve_conservation_law_witness mve_law_trivial_refuse
    metastable_vs_equilibrium_conservation_unwired = mve_law_witness_open /\
  evaluate_mve_conservation_law_witness mve_law_green_invent_refuse
    metastable_vs_equilibrium_conservation_unwired = mve_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-12 pins (structure witnesses — conservation laws not Proved)  *)
(* ------------------------------------------------------------------ *)

Definition metastableVsEquilibriumConservationProved : bool := false.

Lemma metastable_vs_equilibrium_conservation_proved_false :
  metastableVsEquilibriumConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_unwired false false =
  mve_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_unwired false false =
  mve_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_unwired false false) =
  true.
Proof.
  unfold mve_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named C Z=6 close — concurrent **product**                         *)
(* ------------------------------------------------------------------ *)

Lemma c6_witness_named_ok :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
  mve_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_c6_metastable_vs_equilibrium_conservation :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
  mve_verdict_named_ok /\
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumC6Witness = true /\
  carbon_atomic_number_z = 6 /\
  pattern_class_metastable_vs_equilibrium_idx = 12.
Proof.
  repeat split; reflexivity.
Qed.

Lemma mve_named_close_ok :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_proved false false =
  mve_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_metastable_vs_equilibrium_conservation_close :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_proved false false =
  mve_verdict_named_ok /\
  metastable_vs_equilibrium_conservation_authorized false false = true.
Proof.
  split.
  - apply mve_named_close_ok.
  - unfold metastable_vs_equilibrium_conservation_authorized.
    rewrite mve_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — metastable refuse                *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumEmptyWitness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
  mve_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumEmptyWitness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
  mve_verdict_trivial_refuse /\
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_bundle
       metastable_vs_equilibrium_conservation_unwired
       metastableVsEquilibriumEmptyWitness
       metastableVsEquilibriumClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold mve_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse              *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent true false false false false =
  mve_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent true false false false false =
  mve_verdict_xor_refuse /\
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_bundle
       metastable_vs_equilibrium_conservation_unwired
       metastableVsEquilibriumC6Witness
       metastableVsEquilibriumClaimBarAbsent true false false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold mve_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_unwired true false =
  mve_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_unwired true false) =
  false.
Proof.
  unfold mve_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_mve_bundle_refuse :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false true false false false =
  mve_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Fast kinetics ≠ equilibrium G hull — fail-closed                    *)
(* ------------------------------------------------------------------ *)

Lemma fast_kinetics_not_equilibrium_g_hull_refuse :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false true false =
  mve_verdict_fast_kinetics_not_equilibrium_g_hull_refuse.
Proof. reflexivity. Qed.

Theorem fast_kinetics_not_equilibrium_g_hull_fail_closed :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false true false =
  mve_verdict_fast_kinetics_not_equilibrium_g_hull_refuse /\
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_bundle
       metastable_vs_equilibrium_conservation_unwired
       metastableVsEquilibriumC6Witness
       metastableVsEquilibriumClaimBarAbsent false false false true false) =
  false.
Proof.
  split.
  - apply fast_kinetics_not_equilibrium_g_hull_refuse.
  - unfold mve_conservation_verdict_ok.
    rewrite fast_kinetics_not_equilibrium_g_hull_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Time named remainder ≠ new law — fail-closed                        *)
(* ------------------------------------------------------------------ *)

Lemma time_remainder_not_new_law_refuse :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false true =
  mve_verdict_time_remainder_not_new_law_refuse.
Proof. reflexivity. Qed.

Theorem time_remainder_not_new_law_fail_closed :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false true =
  mve_verdict_time_remainder_not_new_law_refuse /\
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_bundle
       metastable_vs_equilibrium_conservation_unwired
       metastableVsEquilibriumC6Witness
       metastableVsEquilibriumClaimBarAbsent false false false false true) =
  false.
Proof.
  split.
  - apply time_remainder_not_new_law_refuse.
  - unfold mve_conservation_verdict_ok.
    rewrite time_remainder_not_new_law_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — metastable refuse                  *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false true false false =
  mve_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false true false false =
  mve_verdict_proved_without_bar_refuse /\
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_bundle
       metastable_vs_equilibrium_conservation_unwired
       metastableVsEquilibriumC6Witness
       metastableVsEquilibriumClaimBarAbsent false false true false false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold mve_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — metastable lattice not wired              *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_proved false true =
  mve_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_proved false true) =
  false.
Proof.
  unfold mve_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel metastability axiom refuse — morphism not 26th axiom         *)
(* ------------------------------------------------------------------ *)

Definition metastableVsEquilibriumConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs".

Definition parallelMetastabilityAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_metastability_axiom_refuse :
  metastableVsEquilibriumConservationAuthority <>
  parallelMetastabilityAxiomTag /\
  metastableVsEquilibriumConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply metastable_vs_equilibrium_conservation_proved_false.
Qed.

Theorem parallel_metastability_axiom_not_minted :
  metastableVsEquilibriumConservationAuthority =
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs" /\
  metastableVsEquilibriumConservationProved = false /\
  metastableVsEquilibriumConservationAuthority <> parallelMetastabilityAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — metastable ≠ L1 SpeciesId occupancy tag  *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition metastableVsEquilibriumConservationFraming : string :=
  "second_law_conservation_metastable_vs_equilibrium_one_axiom".

Lemma species_id_smuggle_refuse :
  metastableVsEquilibriumConservationFraming <>
  speciesIdSmuggleFraming /\
  carbon_atomic_number_z = 6 /\
  pattern_class_metastable_vs_equilibrium_idx = 12.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem metastable_not_species_id_smuggle :
  metastableVsEquilibriumConservationFraming <>
  speciesIdSmuggleFraming /\
  carbon_atomic_number_z = 6 /\
  pattern_class_metastable_vs_equilibrium_idx = 12 /\
  metastableVsEquilibriumConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — metastable ≠ Z=119 smuggle                   *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  metastableVsEquilibriumConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem metastable_not_extra_element_id :
  metastableVsEquilibriumConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_metastable_vs_equilibrium_scaffold".

Lemma tp_float_pin_refuse :
  metastableVsEquilibriumConservationFraming <>
  tpFloatPinFraming /\
  equilibrium_basin_channel_tag = "equilibrium_basin".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  metastableVsEquilibriumConservationFraming <>
  tpFloatPinFraming /\
  metastable_trap_channel_tag = "metastable_trap" /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Metastable-vs-equilibrium **conservation** coherence scaffold       *)
(* ------------------------------------------------------------------ *)

Definition mve_conservation_coherence_scaffold : bool :=
  mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_proved false false) &&
  negb (mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_unwired true false)) &&
  negb (mve_conservation_verdict_ok
    (evaluate_metastable_vs_equilibrium_conservation_close
       metastable_vs_equilibrium_conservation_proved false true)).

Lemma mve_conservation_coherence_scaffold_true :
  mve_conservation_coherence_scaffold = true.
Proof.
  unfold mve_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem mve_conservation_coherence_scaffold_theorem :
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_proved false false =
    mve_verdict_named_ok /\
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_unwired true false =
    mve_verdict_green_invent_refuse /\
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_proved false true =
    mve_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting            *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition mve_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition mve_conservation_knowing_fiber_ok : bool :=
  mve_conservation_fiber_ok fiber_quantum_knowing.

Definition mve_conservation_meso_acting_ok : bool :=
  mve_conservation_fiber_ok fiber_meso_acting.

Lemma mve_conservation_knowing_fiber_ok_true :
  mve_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma mve_conservation_meso_acting_not_ok :
  mve_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem mve_conservation_routes_knowing_not_meso :
  mve_conservation_knowing_fiber_ok = true /\
  mve_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply mve_conservation_knowing_fiber_ok_true.
  - apply mve_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  mve_conservation_knowing_fiber_ok &&
  negb mve_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, mve_conservation_knowing_fiber_ok,
    mve_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-12 + fail-closed + fiber               *)
(* ------------------------------------------------------------------ *)

Theorem metastable_vs_equilibrium_conservation_fixture_scaffold :
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
    mve_verdict_named_ok /\
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumEmptyWitness
    metastableVsEquilibriumClaimBarAbsent false false false false false =
    mve_verdict_trivial_refuse /\
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent true false false false false =
    mve_verdict_xor_refuse /\
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false true false false =
    mve_verdict_proved_without_bar_refuse /\
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false true false =
    mve_verdict_fast_kinetics_not_equilibrium_g_hull_refuse /\
  evaluate_metastable_vs_equilibrium_bundle
    metastable_vs_equilibrium_conservation_unwired
    metastableVsEquilibriumC6Witness
    metastableVsEquilibriumClaimBarAbsent false false false false true =
    mve_verdict_time_remainder_not_new_law_refuse /\
  evaluate_metastable_vs_equilibrium_conservation_close
    metastable_vs_equilibrium_conservation_unwired false false =
    mve_verdict_unwired_ok /\
  mve_conservation_knowing_fiber_ok = true /\
  mve_conservation_meso_acting_ok = false /\
  metastableVsEquilibriumConservationProved = false /\
  mveProductNotXor = true /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — metastable)          *)
(* ------------------------------------------------------------------ *)

Definition chemL0MetastableVsEquilibriumTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs".

Definition metastableEquilibriumEdgeAuthority : string :=
  "umst/umst-chem/src/metastable_equilibrium.rs".

Definition calphadKineticsAuthority : string :=
  "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs".

Definition scale02RemainderAuthority : string :=
  "umst/umst-chem/src/timescale_separation_remainders.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemIntNuanceMetastableCellId : string := "CHEM-INT-NUANCE-METASTABLE".

Definition chemL0EdgeMetastableCellId : string := "CHEM-L0-EDGE-METASTABLE".

Definition chemIntCalphadEquilibriumNotKineticsCellId : string :=
  "CHEM-INT-CALPHAD-EQUILIBRIUM-NOT-KINETICS".

Definition chemL0Scale02CellId : string := "CHEM-L0-SCALE-02".

Definition metastableVsEquilibriumConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-METASTABLE-VS-EQUILIBRIUM-CONSERVATION".

Definition kineticsRemainderRowName : string := "reaction_kinetics".

Definition metastableVsEquilibriumConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-METASTABLE-VS-EQUILIBRIUM-CONSERVATION MetastableVsEquilibriumConservationModality Unwired Assumed Proved Surrogate four-step lattice metastableVsEquilibriumConservationProved false evaluateMetastableVsEquilibriumBundle evaluateMetastableVsEquilibriumConservation named class 12 metastable_vs_equilibrium C Z=6 equilibrium basin metastable trap concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel metastability axiom refuse species id smuggle refuse extra element id Z=119 refuse fast kinetics not equilibrium G hull refuse time remainder not new law refuse metastable ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma metastable_vs_equilibrium_conservation_cell_id :
  metastableVsEquilibriumConservationCellId =
  "CHEM-FORMAL-Q-COQ-METASTABLE-VS-EQUILIBRIUM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_l0_table :
  chemL0MetastableVsEquilibriumTableAuthority <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_authority_path :
  metastableVsEquilibriumConservationAuthority =
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs".
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_edge :
  metastableEquilibriumEdgeAuthority <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_calphad_kinetics :
  calphadKineticsAuthority <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_scale02_remainder :
  scale02RemainderAuthority <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_marker :
  mveConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_nuance_cell :
  chemIntNuanceMetastableCellId = "CHEM-INT-NUANCE-METASTABLE".
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_edge_cell :
  chemL0EdgeMetastableCellId = "CHEM-L0-EDGE-METASTABLE".
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_calphad_cell :
  chemIntCalphadEquilibriumNotKineticsCellId =
  "CHEM-INT-CALPHAD-EQUILIBRIUM-NOT-KINETICS".
Proof. reflexivity. Qed.

Lemma metastable_vs_equilibrium_conservation_cites_scale02_cell :
  chemL0Scale02CellId = "CHEM-L0-SCALE-02".
Proof. reflexivity. Qed.

Lemma kinetics_remainder_row_named :
  kineticsRemainderRowName = "reaction_kinetics".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom     *)
(* ------------------------------------------------------------------ *)

Lemma metastable_vs_equilibrium_not_26th_axiom :
  metastableVsEquilibriumConservationFraming <> parallelMetastabilityAxiomTag.
Proof. discriminate. Qed.

Lemma metastable_vs_equilibrium_second_law_conservation_framing :
  metastableVsEquilibriumConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma metastable_vs_equilibrium_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma metastable_vs_equilibrium_conservation_modality_unwired :
  metastableVsEquilibriumConservationModalityCurrent =
  metastable_vs_equilibrium_conservation_unwired.
Proof. reflexivity. Qed.

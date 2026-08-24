(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PatternProductConservation.v                          *)
(*                                                                      *)
(*  Knowing-fiber Coq: PATTERN-00 PatternBundle **product**            *)
(*  **conservation**. Concurrent Π_c identity conserved (cardinality   *)
(*  25; ≥2 Present slots is **product**, not XOR). XOR mutually-      *)
(*  exclusive classifiers refuse; carbon nuance witness: allotrope +     *)
(*  catalysis + continuum concurrent. Trivial empty-bundle fail-closed; *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed. Geometry  *)
(*  routes knowing/quantum fiber not meso acting. Not 118² GREEN table. *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — pattern **product** is not a second     *)
(*  axiom.                                                              *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 pattern **product** **conservation** modality             *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive PatternProductConservationModality : Type :=
  | pattern_product_conservation_unwired
  | pattern_product_conservation_assumed
  | pattern_product_conservation_proved
  | pattern_product_conservation_surrogate.

Definition patternProductConservationModalityCurrent : PatternProductConservationModality :=
  pattern_product_conservation_unwired.

Definition pattern_product_lattice_cardinality : nat := 4.

Lemma pattern_product_lattice_cardinality_is_four :
  pattern_product_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma pattern_product_lattice_not_118_squared :
  negb (Nat.eqb pattern_product_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold pattern_product_lattice_cardinality.
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

Definition pattern_class_allotrope_idx : nat := 10.
Definition pattern_class_catalysis_idx : nat := 14.
Definition pattern_class_continuum_idx : nat := 23.

Lemma pattern_class_allotrope_idx_is_10 :
  pattern_class_allotrope_idx = 10.
Proof. reflexivity. Qed.

Lemma pattern_class_catalysis_idx_is_14 :
  pattern_class_catalysis_idx = 14.
Proof. reflexivity. Qed.

Lemma pattern_class_continuum_idx_is_23 :
  pattern_class_continuum_idx = 23.
Proof. reflexivity. Qed.

Lemma pattern_class_carbon_indices_valid :
  pattern_class_index_valid pattern_class_allotrope_idx = true /\
  pattern_class_index_valid pattern_class_catalysis_idx = true /\
  pattern_class_index_valid pattern_class_continuum_idx = true.
Proof.
  repeat split; unfold pattern_class_index_valid, pattern_class_cardinality;
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PatternBundle slot — concurrent **product** factor, not XOR bucket  *)
(* ------------------------------------------------------------------ *)

Inductive pattern_bundle_slot : Type :=
  | bundle_slot_unwired
  | bundle_slot_absent
  | bundle_slot_present.

Definition pattern_bundle_slot_beq (s1 s2 : pattern_bundle_slot) : bool :=
  match s1, s2 with
  | bundle_slot_unwired, bundle_slot_unwired => true
  | bundle_slot_absent, bundle_slot_absent => true
  | bundle_slot_present, bundle_slot_present => true
  | _, _ => false
  end.

Definition pattern_bundle_slot_is_present (s : pattern_bundle_slot) : bool :=
  match s with
  | bundle_slot_present => true
  | _ => false
  end.

Definition pattern_bundle_slot_is_unwired (s : pattern_bundle_slot) : bool :=
  match s with
  | bundle_slot_unwired => true
  | _ => false
  end.

Definition patternBundleUnwiredSlot : pattern_bundle_slot := bundle_slot_unwired.

Definition patternBundleAbsentSlot : pattern_bundle_slot := bundle_slot_absent.

Definition patternBundlePresentSlot : pattern_bundle_slot := bundle_slot_present.

Lemma present_slot_is_present :
  pattern_bundle_slot_is_present bundle_slot_present = true.
Proof. reflexivity. Qed.

Lemma unwired_slot_not_present :
  pattern_bundle_slot_is_present bundle_slot_unwired = false.
Proof. reflexivity. Qed.

Lemma absent_slot_not_present :
  pattern_bundle_slot_is_present bundle_slot_absent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  PatternBundle_25 — Π_c concurrent **product** scaffold              *)
(* ------------------------------------------------------------------ *)

Definition pattern_bundle : Type := nat -> pattern_bundle_slot.

Definition patternBundleAllUnwired : pattern_bundle :=
  fun _ => bundle_slot_unwired.

Definition patternBundleAt (b : pattern_bundle) (idx : nat)
  (slot : pattern_bundle_slot) : pattern_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition patternBundleWithPresent (b : pattern_bundle) (idx : nat) : pattern_bundle :=
  patternBundleAt b idx bundle_slot_present.

Fixpoint count_present_up_to (b : pattern_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if pattern_bundle_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_present_up_to b i + add
  end.

Definition patternBundlePresentCount (b : pattern_bundle) : nat :=
  count_present_up_to b pattern_class_cardinality.

Definition patternBundleHolds (b : pattern_bundle) (idx : nat) : bool :=
  pattern_bundle_slot_is_present (b idx).

Definition patternBundleIsConcurrentProduct (b : pattern_bundle) : bool :=
  Nat.leb 2 (patternBundlePresentCount b).

Fixpoint pattern_bundle_slots_match_up_to
  (b1 b2 : pattern_bundle) (bound : nat) : bool :=
  match bound with
  | 0 => true
  | S i =>
      pattern_bundle_slot_beq (b1 (pred bound)) (b2 (pred bound)) &&
      pattern_bundle_slots_match_up_to b1 b2 i
  end.

Definition patternBundleIdentityConserved (b1 b2 : pattern_bundle) : bool :=
  pattern_bundle_slots_match_up_to b1 b2 pattern_class_cardinality.

(* Carbon nuance witness: allotrope + catalysis + continuum concurrent. *)
Definition patternBundleCarbonNuanceWitness : pattern_bundle :=
  patternBundleWithPresent
    (patternBundleWithPresent
      (patternBundleWithPresent patternBundleAllUnwired
        pattern_class_allotrope_idx)
      pattern_class_catalysis_idx)
    pattern_class_continuum_idx.

Definition patternBundleEmptyWitness : pattern_bundle :=
  patternBundleAllUnwired.

Definition patternBundleSinglePresent : pattern_bundle :=
  patternBundleWithPresent patternBundleAllUnwired pattern_class_allotrope_idx.

Lemma carbon_nuance_allotrope_present :
  patternBundleHolds patternBundleCarbonNuanceWitness pattern_class_allotrope_idx = true.
Proof. reflexivity. Qed.

Lemma carbon_nuance_catalysis_present :
  patternBundleHolds patternBundleCarbonNuanceWitness pattern_class_catalysis_idx = true.
Proof. reflexivity. Qed.

Lemma carbon_nuance_continuum_present :
  patternBundleHolds patternBundleCarbonNuanceWitness pattern_class_continuum_idx = true.
Proof. reflexivity. Qed.

Lemma carbon_nuance_present_count_is_three :
  patternBundlePresentCount patternBundleCarbonNuanceWitness = 3.
Proof. reflexivity. Qed.

Lemma carbon_nuance_is_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleCarbonNuanceWitness = true.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite carbon_nuance_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  patternBundlePresentCount patternBundleEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleEmptyWitness = false.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  patternBundlePresentCount patternBundleSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleSinglePresent = false.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

Lemma carbon_nuance_identity_conserved :
  patternBundleIdentityConserved patternBundleCarbonNuanceWitness
    patternBundleCarbonNuanceWitness = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive xor_classifier_bucket : Type :=
  | xor_bucket_exclusive
  | xor_bucket_concurrent_product.

Definition xorClassifierMarker : string := "chem_l0_pattern_xor_classifier_v1".
Definition concurrentProductMarker : string := "chem_int_pattern_bundle_product_v1".

Lemma xor_marker_ne_concurrent_product_marker :
  xorClassifierMarker <> concurrentProductMarker.
Proof. discriminate. Qed.

Definition xorClassifierIncompatible (claim_xor : bool) (b : pattern_bundle) : bool :=
  claim_xor && patternBundleIsConcurrentProduct b.

Lemma xor_refuse_on_carbon_nuance :
  xorClassifierIncompatible true patternBundleCarbonNuanceWitness = true.
Proof.
  unfold xorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma xor_ok_on_concurrent_product_claim :
  xorClassifierIncompatible false patternBundleCarbonNuanceWitness = false.
Proof. reflexivity. Qed.

Definition productNotXor : bool :=
  patternBundleIsConcurrentProduct patternBundleCarbonNuanceWitness &&
  xorClassifierIncompatible true patternBundleCarbonNuanceWitness.

Lemma product_not_xor_true : productNotXor = true.
Proof.
  unfold productNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  productNotXor = true /\
  Nat.leb 2 (patternBundlePresentCount patternBundleCarbonNuanceWitness) = true /\
  xorClassifierMarker <> concurrentProductMarker.
Proof.
  split.
  - apply product_not_xor_true.
  - split.
    + rewrite carbon_nuance_present_count_is_three.
      reflexivity.
    + apply xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern **product** bar — Proved-without-bar fail-closed             *)
(* ------------------------------------------------------------------ *)

Inductive pattern_product_bar_presence : Type :=
  | pattern_product_bar_absent
  | pattern_product_bar_present.

Record pattern_claim_product_bar : Type := {
  pattern_bar_presence : pattern_product_bar_presence;
  pattern_product_bar_defect_total : nat
}.

Definition patternClaimProductBarAbsent : pattern_claim_product_bar :=
  {| pattern_bar_presence := pattern_product_bar_absent;
     pattern_product_bar_defect_total := 0 |}.

Definition patternClaimProductBarZeroDefect : pattern_claim_product_bar :=
  {| pattern_bar_presence := pattern_product_bar_present;
     pattern_product_bar_defect_total := 0 |}.

Definition pattern_claim_product_bar_zero_defect (b : pattern_claim_product_bar) : bool :=
  match pattern_bar_presence b with
  | pattern_product_bar_absent => false
  | pattern_product_bar_present =>
      Nat.eqb (pattern_product_bar_defect_total b) 0
  end.

Lemma pattern_claim_product_bar_zero_defect_true :
  pattern_claim_product_bar_zero_defect patternClaimProductBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma pattern_claim_product_bar_absent_not_zero_defect :
  pattern_claim_product_bar_zero_defect patternClaimProductBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern **product** **conservation** verdict — fail-closed lattice  *)
(* ------------------------------------------------------------------ *)

Inductive pattern_product_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_product_named_ok
  | verdict_trivial_bundle_refuse
  | verdict_xor_classifier_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition pattern_product_conservation_verdict_ok
  (v : pattern_product_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_product_named_ok => true
  | _ => false
  end.

Definition pattern_product_conservation_verdict_beq
  (v1 v2 : pattern_product_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_product_named_ok, verdict_product_named_ok => true
  | verdict_trivial_bundle_refuse, verdict_trivial_bundle_refuse => true
  | verdict_xor_classifier_refuse, verdict_xor_classifier_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition patternBundleNontrivial (b : pattern_bundle) : bool :=
  Nat.ltb 0 (patternBundlePresentCount b).

Definition evaluate_pattern_bundle
  (m : PatternProductConservationModality)
  (b : pattern_bundle)
  (bar : pattern_claim_product_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : pattern_product_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (patternBundleNontrivial b)
            then verdict_trivial_bundle_refuse
            else if xorClassifierIncompatible claim_xor_classifier b
                 then verdict_xor_classifier_refuse
                 else
                   match m with
                   | pattern_product_conservation_unwired => verdict_product_named_ok
                   | pattern_product_conservation_assumed
                   | pattern_product_conservation_surrogate => verdict_unwired_ok
                   | pattern_product_conservation_proved =>
                       verdict_proved_without_bar_refuse
                   end.

Definition evaluate_pattern_product_conservation_close
  (m : PatternProductConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : pattern_product_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | pattern_product_conservation_unwired => verdict_unwired_ok
    | pattern_product_conservation_assumed
    | pattern_product_conservation_proved
    | pattern_product_conservation_surrogate => verdict_product_named_ok
    end.

Definition pattern_product_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_pattern_product_conservation_close
          pattern_product_conservation_proved claim_physics_green claim_production_wired with
  | verdict_product_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Pattern **product** **conservation** law cells — four laws, Unwired  *)
(* ------------------------------------------------------------------ *)

Inductive pattern_product_conservation_law : Type :=
  | law_pattern_product_named
  | law_xor_classifier_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition pattern_product_conservation_law_count : nat := 4.

Lemma pattern_product_conservation_law_count_is_four :
  pattern_product_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive pattern_product_conservation_law_witness : Type :=
  | pattern_product_law_witness_open
  | pattern_product_law_witness_proved.

Definition evaluate_pattern_product_conservation_law_witness
  (law : pattern_product_conservation_law) (m : PatternProductConservationModality)
  : pattern_product_conservation_law_witness :=
  match m with
  | pattern_product_conservation_unwired
  | pattern_product_conservation_assumed
  | pattern_product_conservation_surrogate => pattern_product_law_witness_open
  | pattern_product_conservation_proved => pattern_product_law_witness_proved
  end.

Lemma all_pattern_product_conservation_laws_open_at_unwired :
  evaluate_pattern_product_conservation_law_witness law_pattern_product_named
    pattern_product_conservation_unwired = pattern_product_law_witness_open /\
  evaluate_pattern_product_conservation_law_witness law_xor_classifier_refuse
    pattern_product_conservation_unwired = pattern_product_law_witness_open /\
  evaluate_pattern_product_conservation_law_witness law_green_invent_refuse
    pattern_product_conservation_unwired = pattern_product_law_witness_open /\
  evaluate_pattern_product_conservation_law_witness law_production_wired_refuse
    pattern_product_conservation_unwired = pattern_product_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 pins (structure witnesses — **product** laws not Proved) *)
(* ------------------------------------------------------------------ *)

Definition pattern00ProductProved : bool := false.

Lemma pattern00_product_proved_false : pattern00ProductProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_unwired false false) =
  true.
Proof.
  unfold pattern_product_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named carbon nuance close — concurrent **product** **conservation** *)
(* ------------------------------------------------------------------ *)

Lemma carbon_nuance_named_ok :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false false =
  verdict_product_named_ok.
Proof. reflexivity. Qed.

Theorem named_carbon_nuance_pattern_product_conservation :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false false =
  verdict_product_named_ok /\
  patternBundleIdentityConserved patternBundleCarbonNuanceWitness
    patternBundleCarbonNuanceWitness = true /\
  patternBundleIsConcurrentProduct patternBundleCarbonNuanceWitness = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma pattern_product_named_close_ok :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_proved false false =
  verdict_product_named_ok.
Proof. reflexivity. Qed.

Theorem named_pattern_product_conservation_close :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_proved false false =
  verdict_product_named_ok /\
  pattern_product_conservation_authorized false false = true.
Proof.
  split.
  - apply pattern_product_named_close_ok.
  - unfold pattern_product_conservation_authorized.
    rewrite pattern_product_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — pattern **product** refuse        *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleEmptyWitness
    patternClaimProductBarAbsent false false false =
  verdict_trivial_bundle_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleEmptyWitness
    patternClaimProductBarAbsent false false false =
  verdict_trivial_bundle_refuse /\
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_bundle
       pattern_product_conservation_unwired patternBundleEmptyWitness
       patternClaimProductBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold pattern_product_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse              *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent true false false =
  verdict_xor_classifier_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent true false false =
  verdict_xor_classifier_refuse /\
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_bundle
       pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
       patternClaimProductBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold pattern_product_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_unwired true false) =
  false.
Proof.
  unfold pattern_product_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_pattern_bundle_refuse :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — pattern **product** refuse          *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false true =
  verdict_proved_without_bar_refuse /\
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_bundle
       pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
       patternClaimProductBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold pattern_product_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarZeroDefect false false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — pattern lattice not production wired      *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  pattern_product_conservation_verdict_ok
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_proved false true) =
  false.
Proof.
  unfold pattern_product_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern **product** **conservation** coherence scaffold             *)
(* ------------------------------------------------------------------ *)

Definition pattern_product_conservation_coherence_scaffold : bool :=
  pattern_product_conservation_verdict_beq
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_proved false false)
    verdict_product_named_ok &&
  pattern_product_conservation_verdict_beq
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_unwired true false)
    verdict_green_invent_refuse &&
  pattern_product_conservation_verdict_beq
    (evaluate_pattern_product_conservation_close
       pattern_product_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma pattern_product_conservation_coherence_scaffold_true :
  pattern_product_conservation_coherence_scaffold = true.
Proof.
  unfold pattern_product_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem pattern_product_conservation_coherence_scaffold_theorem :
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_proved false false =
    verdict_product_named_ok /\
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_proved false true =
    verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_pattern_product_conservation.

Definition pattern_product_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition pattern_product_conservation_knowing_fiber_ok : bool :=
  pattern_product_conservation_fiber_ok fiber_quantum_knowing.

Definition pattern_product_conservation_meso_acting_ok : bool :=
  pattern_product_conservation_fiber_ok fiber_meso_acting.

Lemma pattern_product_conservation_knowing_fiber_ok_true :
  pattern_product_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma pattern_product_conservation_meso_acting_not_ok :
  pattern_product_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem pattern_product_conservation_routes_knowing_not_meso :
  pattern_product_conservation_knowing_fiber_ok = true /\
  pattern_product_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply pattern_product_conservation_knowing_fiber_ok_true.
  - apply pattern_product_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  pattern_product_conservation_knowing_fiber_ok &&
  negb pattern_product_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, pattern_product_conservation_knowing_fiber_ok,
    pattern_product_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named **product** + fail-closed + fiber + PATTERN-00 *)
(* ------------------------------------------------------------------ *)

Theorem pattern_product_conservation_fixture_scaffold :
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false false =
    verdict_product_named_ok /\
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleEmptyWitness
    patternClaimProductBarAbsent false false false =
    verdict_trivial_bundle_refuse /\
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent true false false =
    verdict_xor_classifier_refuse /\
  evaluate_pattern_bundle
    pattern_product_conservation_unwired patternBundleCarbonNuanceWitness
    patternClaimProductBarAbsent false false true =
    verdict_proved_without_bar_refuse /\
  evaluate_pattern_product_conservation_close
    pattern_product_conservation_unwired false false =
    verdict_unwired_ok /\
  pattern_product_conservation_knowing_fiber_ok = true /\
  pattern_product_conservation_meso_acting_ok = false /\
  pattern00ProductProved = false /\
  productNotXor = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pattern product) *)
(* ------------------------------------------------------------------ *)

Definition patternTaxonomyAuthority : string :=
  "umst/umst-chem/src/pattern_taxonomy.rs".

Definition chemL0Pattern00Authority : string :=
  "CHEM-L0-PATTERN-00".

Definition chemIntPatternBundleProductAuthority : string :=
  "CHEM-INT-PATTERN-BUNDLE-PRODUCT".

Definition patternProductConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PATTERN-PRODUCT-CONSERVATION".

Definition patternProductConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PATTERN-PRODUCT-CONSERVATION PATTERN-00 PatternBundle product conservation concurrent Pi_c identity conserved cardinality 25 present slots product not XOR xor mutually exclusive classifiers refuse carbon nuance witness allotrope catalysis continuum concurrent trivial empty bundle fail-closed GREEN invent fail-closed proved-without-bar fail-closed pattern00ProductProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second product axiom not GREEN DFT not physics GREEN not production_wired".

Lemma pattern_product_conservation_cell_id :
  patternProductConservationCellId =
  "CHEM-FORMAL-Q-COQ-PATTERN-PRODUCT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma pattern_product_conservation_cites_pattern_taxonomy_rs :
  patternTaxonomyAuthority <> "".
Proof. discriminate. Qed.

Lemma pattern_product_conservation_cites_l0_pattern_00 :
  chemL0Pattern00Authority = "CHEM-L0-PATTERN-00".
Proof. reflexivity. Qed.

Lemma pattern_product_conservation_cites_int_pattern_bundle_product :
  chemIntPatternBundleProductAuthority = "CHEM-INT-PATTERN-BUNDLE-PRODUCT".
Proof. reflexivity. Qed.

Lemma pattern_product_conservation_cites_marker :
  concurrentProductMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not second product *)
(* ------------------------------------------------------------------ *)

Definition patternProductSecondLawConservationFraming : string :=
  "second_law_conservation_pattern_product_one_axiom_not_second_product_axiom".

Lemma pattern_product_not_second_product_axiom :
  patternProductSecondLawConservationFraming <> "second_product_axiom".
Proof. discriminate. Qed.

Lemma pattern_product_second_law_conservation_framing :
  patternProductSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma pattern_product_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma pattern_product_conservation_modality_unwired :
  patternProductConservationModalityCurrent = pattern_product_conservation_unwired.
Proof. reflexivity. Qed.

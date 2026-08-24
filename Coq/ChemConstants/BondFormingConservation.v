(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: BondFormingConservation.v                             *)
(*                                                                      *)
(*  Knowing-fiber Coq: PATTERN-00 class 2 Bond-forming **conservation**. *)
(*  Concurrent Π_c identity conserved (cardinality 25; ≥2 Present slots *)
(*  is **product**, not XOR). QTAIM BCP + Mayer/DDEC named; forming     *)
(*  arrow is Kleisli Interact Apply — **not** Refine. XOR mutually-     *)
(*  exclusive classifiers refuse; bond-forming + shared nuance witness  *)
(*  concurrent. Trivial empty-bundle fail-closed; GREEN invent fail-    *)
(*  closed; Proved-without-bar fail-closed. Geometry routes knowing/    *)
(*  quantum fiber not meso acting. Not 118² GREEN table.                *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — bond-forming is witness not second axiom.  *)
(*  INT: umst/umst-chem/src/x_rows/bond_forming_conservation.rs        *)
(*  (read-only cite).                                                   *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 class 2 Bond-forming **conservation** modality           *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive BondFormingConservationModality : Type :=
  | bond_forming_conservation_unwired
  | bond_forming_conservation_assumed
  | bond_forming_conservation_proved
  | bond_forming_conservation_surrogate.

Definition bondFormingConservationModalityCurrent : BondFormingConservationModality :=
  bond_forming_conservation_unwired.

Definition bond_forming_lattice_cardinality : nat := 4.

Lemma bond_forming_lattice_cardinality_is_four :
  bond_forming_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma bond_forming_lattice_not_118_squared :
  negb (Nat.eqb bond_forming_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold bond_forming_lattice_cardinality.
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

(* North-star §2 class 1 Shared + class 2 Bond-forming indices. *)
Definition pattern_class_shared_idx : nat := 1.
Definition pattern_class_bond_forming_idx : nat := 2.

Lemma pattern_class_shared_idx_is_1 :
  pattern_class_shared_idx = 1.
Proof. reflexivity. Qed.

Lemma pattern_class_bond_forming_idx_is_2 :
  pattern_class_bond_forming_idx = 2.
Proof. reflexivity. Qed.

Lemma pattern_class_bond_forming_indices_valid :
  pattern_class_index_valid pattern_class_shared_idx = true /\
  pattern_class_index_valid pattern_class_bond_forming_idx = true.
Proof.
  repeat split; unfold pattern_class_index_valid, pattern_class_cardinality;
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Forming channel — Kleisli Interact Apply not Refine separation      *)
(* ------------------------------------------------------------------ *)

Inductive forming_channel : Type :=
  | forming_interact_apply
  | forming_refine_separation.

Definition forming_channel_is_interact_apply (c : forming_channel) : bool :=
  match c with
  | forming_interact_apply => true
  | _ => false
  end.

Definition forming_channel_is_refine_separation (c : forming_channel) : bool :=
  match c with
  | forming_refine_separation => true
  | _ => false
  end.

Lemma interact_apply_is_interact :
  forming_channel_is_interact_apply forming_interact_apply = true.
Proof. reflexivity. Qed.

Lemma interact_apply_not_refine_separation :
  forming_channel_is_refine_separation forming_interact_apply = false.
Proof. reflexivity. Qed.

Lemma refine_separation_not_interact_apply :
  forming_channel_is_interact_apply forming_refine_separation = false.
Proof. reflexivity. Qed.

Definition qtaimBcpTag : string := "QTAIM BCP".
Definition interactApplyTag : string := "Kleisli Interact Apply".
Definition mayerDdecTag : string := "Mayer/DDEC".

Lemma qtaim_bcp_tag_nonempty : qtaimBcpTag <> "".
Proof. discriminate. Qed.

Lemma interact_apply_tag_nonempty : interactApplyTag <> "".
Proof. discriminate. Qed.

Definition interactNeRefineCollision : string :=
  "interact_ne_refine_forming_collision_v1".

Lemma interact_ne_refine_collision_nonempty :
  interactNeRefineCollision <> "".
Proof. discriminate. Qed.

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

Definition patternBundleUnwiredSlot : pattern_bundle_slot := bundle_slot_unwired.
Definition patternBundlePresentSlot : pattern_bundle_slot := bundle_slot_present.

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

(* Bond-forming + shared nuance witness: class 1 + class 2 concurrent. *)
Definition patternBundleBondFormingSharedWitness : pattern_bundle :=
  patternBundleWithPresent
    (patternBundleWithPresent patternBundleAllUnwired
      pattern_class_shared_idx)
    pattern_class_bond_forming_idx.

Definition patternBundleEmptyWitness : pattern_bundle :=
  patternBundleAllUnwired.

Definition patternBundleSinglePresent : pattern_bundle :=
  patternBundleWithPresent patternBundleAllUnwired pattern_class_bond_forming_idx.

Lemma bond_forming_shared_shared_present :
  patternBundleHolds patternBundleBondFormingSharedWitness pattern_class_shared_idx = true.
Proof. reflexivity. Qed.

Lemma bond_forming_shared_bond_forming_present :
  patternBundleHolds patternBundleBondFormingSharedWitness pattern_class_bond_forming_idx = true.
Proof. reflexivity. Qed.

Lemma bond_forming_shared_present_count_is_two :
  patternBundlePresentCount patternBundleBondFormingSharedWitness = 2.
Proof. reflexivity. Qed.

Lemma bond_forming_shared_is_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleBondFormingSharedWitness = true.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite bond_forming_shared_present_count_is_two.
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

Lemma bond_forming_shared_identity_conserved :
  patternBundleIdentityConserved patternBundleBondFormingSharedWitness
    patternBundleBondFormingSharedWitness = true.
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

Lemma xor_refuse_on_bond_forming_shared :
  xorClassifierIncompatible true patternBundleBondFormingSharedWitness = true.
Proof.
  unfold xorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma xor_ok_on_concurrent_product_claim :
  xorClassifierIncompatible false patternBundleBondFormingSharedWitness = false.
Proof. reflexivity. Qed.

Definition productNotXor : bool :=
  patternBundleIsConcurrentProduct patternBundleBondFormingSharedWitness &&
  xorClassifierIncompatible true patternBundleBondFormingSharedWitness.

Lemma product_not_xor_true : productNotXor = true.
Proof.
  unfold productNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  productNotXor = true /\
  Nat.leb 2 (patternBundlePresentCount patternBundleBondFormingSharedWitness) = true /\
  xorClassifierMarker <> concurrentProductMarker.
Proof.
  split.
  - apply product_not_xor_true.
  - split.
    + rewrite bond_forming_shared_present_count_is_two.
      reflexivity.
    + apply xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact Apply not Refine — forming arrow separation refuse         *)
(* ------------------------------------------------------------------ *)

Definition formingArrowIsInteractNotRefine : bool :=
  forming_channel_is_interact_apply forming_interact_apply &&
  negb (forming_channel_is_refine_separation forming_interact_apply).

Lemma forming_arrow_interact_not_refine :
  formingArrowIsInteractNotRefine = true.
Proof.
  unfold formingArrowIsInteractNotRefine.
  reflexivity.
Qed.

Definition refineAsFormingArrowRefused (claim_refine_forming : bool) : bool :=
  claim_refine_forming &&
  forming_channel_is_interact_apply forming_interact_apply.

Lemma refine_as_forming_arrow_refused_false :
  refineAsFormingArrowRefused false = false.
Proof. reflexivity. Qed.

Lemma refine_as_forming_arrow_claim_refused :
  refineAsFormingArrowRefused true = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Bond-forming **conservation** bar — Proved-without-bar fail-closed    *)
(* ------------------------------------------------------------------ *)

Inductive bond_forming_bar_presence : Type :=
  | bond_forming_bar_absent
  | bond_forming_bar_present.

Record bond_claim_forming_bar : Type := {
  bond_bar_presence : bond_forming_bar_presence;
  bond_forming_bar_defect_total : nat
}.

Definition bondClaimFormingBarAbsent : bond_claim_forming_bar :=
  {| bond_bar_presence := bond_forming_bar_absent;
     bond_forming_bar_defect_total := 0 |}.

Definition bondClaimFormingBarZeroDefect : bond_claim_forming_bar :=
  {| bond_bar_presence := bond_forming_bar_present;
     bond_forming_bar_defect_total := 0 |}.

Definition bond_claim_forming_bar_zero_defect (b : bond_claim_forming_bar) : bool :=
  match bond_bar_presence b with
  | bond_forming_bar_absent => false
  | bond_forming_bar_present =>
      Nat.eqb (bond_forming_bar_defect_total b) 0
  end.

Lemma bond_claim_forming_bar_zero_defect_true :
  bond_claim_forming_bar_zero_defect bondClaimFormingBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma bond_claim_forming_bar_absent_not_zero_defect :
  bond_claim_forming_bar_zero_defect bondClaimFormingBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Bond-forming **conservation** verdict — fail-closed lattice         *)
(* ------------------------------------------------------------------ *)

Inductive bond_forming_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_bond_forming_named_ok
  | verdict_trivial_bundle_refuse
  | verdict_xor_classifier_refuse
  | verdict_refine_forming_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition bond_forming_conservation_verdict_ok
  (v : bond_forming_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_bond_forming_named_ok => true
  | _ => false
  end.

Definition patternBundleNontrivial (b : pattern_bundle) : bool :=
  Nat.ltb 0 (patternBundlePresentCount b).

Definition evaluate_bond_forming_bundle
  (m : BondFormingConservationModality)
  (b : pattern_bundle)
  (bar : bond_claim_forming_bar)
  (claim_xor_classifier : bool)
  (claim_refine_forming : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : bond_forming_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_refine_forming
            then verdict_refine_forming_refuse
            else if negb (patternBundleNontrivial b)
                 then verdict_trivial_bundle_refuse
                 else if xorClassifierIncompatible claim_xor_classifier b
                      then verdict_xor_classifier_refuse
                      else
                        match m with
                        | bond_forming_conservation_unwired => verdict_bond_forming_named_ok
                        | bond_forming_conservation_assumed
                        | bond_forming_conservation_surrogate => verdict_unwired_ok
                        | bond_forming_conservation_proved =>
                            verdict_proved_without_bar_refuse
                        end.

Definition evaluate_bond_forming_conservation_close
  (m : BondFormingConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bond_forming_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | bond_forming_conservation_unwired => verdict_unwired_ok
    | bond_forming_conservation_assumed
    | bond_forming_conservation_proved
    | bond_forming_conservation_surrogate => verdict_bond_forming_named_ok
    end.

Definition bond_forming_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_bond_forming_conservation_close
          bond_forming_conservation_proved claim_physics_green claim_production_wired with
  | verdict_bond_forming_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Bond-forming **conservation** law cells — four laws, Unwired        *)
(* ------------------------------------------------------------------ *)

Inductive bond_forming_conservation_law : Type :=
  | law_bond_forming_named
  | law_xor_classifier_refuse
  | law_refine_forming_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition bond_forming_conservation_law_count : nat := 5.

Lemma bond_forming_conservation_law_count_is_five :
  bond_forming_conservation_law_count = 5.
Proof. reflexivity. Qed.

Inductive bond_forming_conservation_law_witness : Type :=
  | bond_forming_law_witness_open
  | bond_forming_law_witness_proved.

Definition evaluate_bond_forming_conservation_law_witness
  (law : bond_forming_conservation_law) (m : BondFormingConservationModality)
  : bond_forming_conservation_law_witness :=
  match m with
  | bond_forming_conservation_unwired
  | bond_forming_conservation_assumed
  | bond_forming_conservation_surrogate => bond_forming_law_witness_open
  | bond_forming_conservation_proved => bond_forming_law_witness_proved
  end.

Lemma all_bond_forming_conservation_laws_open_at_unwired :
  evaluate_bond_forming_conservation_law_witness law_bond_forming_named
    bond_forming_conservation_unwired = bond_forming_law_witness_open /\
  evaluate_bond_forming_conservation_law_witness law_xor_classifier_refuse
    bond_forming_conservation_unwired = bond_forming_law_witness_open /\
  evaluate_bond_forming_conservation_law_witness law_refine_forming_refuse
    bond_forming_conservation_unwired = bond_forming_law_witness_open /\
  evaluate_bond_forming_conservation_law_witness law_green_invent_refuse
    bond_forming_conservation_unwired = bond_forming_law_witness_open /\
  evaluate_bond_forming_conservation_law_witness law_production_wired_refuse
    bond_forming_conservation_unwired = bond_forming_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 pins (structure witnesses — bond-forming laws not Proved) *)
(* ------------------------------------------------------------------ *)

Definition bondFormingProved : bool := false.

Lemma bond_forming_proved_false : bondFormingProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

Definition interactNotRefine : bool := true.

Lemma interact_not_refine_pin : interactNotRefine = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_unwired false false) =
  true.
Proof.
  unfold bond_forming_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named bond-forming + shared close — concurrent **conservation**     *)
(* ------------------------------------------------------------------ *)

Lemma bond_forming_shared_named_ok :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false false =
  verdict_bond_forming_named_ok.
Proof. reflexivity. Qed.

Theorem named_bond_forming_shared_conservation :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false false =
  verdict_bond_forming_named_ok /\
  patternBundleIdentityConserved patternBundleBondFormingSharedWitness
    patternBundleBondFormingSharedWitness = true /\
  patternBundleIsConcurrentProduct patternBundleBondFormingSharedWitness = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma bond_forming_named_close_ok :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_proved false false =
  verdict_bond_forming_named_ok.
Proof. reflexivity. Qed.

Theorem named_bond_forming_conservation_close :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_proved false false =
  verdict_bond_forming_named_ok /\
  bond_forming_conservation_authorized false false = true.
Proof.
  split.
  - apply bond_forming_named_close_ok.
  - unfold bond_forming_conservation_authorized.
    rewrite bond_forming_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — bond-forming refuse              *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleEmptyWitness
    bondClaimFormingBarAbsent false false false false =
  verdict_trivial_bundle_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleEmptyWitness
    bondClaimFormingBarAbsent false false false false =
  verdict_trivial_bundle_refuse /\
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_bundle
       bond_forming_conservation_unwired patternBundleEmptyWitness
       bondClaimFormingBarAbsent false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold bond_forming_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse              *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent true false false false =
  verdict_xor_classifier_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent true false false false =
  verdict_xor_classifier_refuse /\
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_bundle
       bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
       bondClaimFormingBarAbsent true false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold bond_forming_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Refine forming refuse — Interact not Refine fail-closed             *)
(* ------------------------------------------------------------------ *)

Lemma refine_forming_refused :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false true false false =
  verdict_refine_forming_refuse.
Proof. reflexivity. Qed.

Theorem refine_forming_arrow_fail_closed :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false true false false =
  verdict_refine_forming_refuse /\
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_bundle
       bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
       bondClaimFormingBarAbsent false true false false) =
  false.
Proof.
  split.
  - apply refine_forming_refused.
  - unfold bond_forming_conservation_verdict_ok.
    rewrite refine_forming_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_unwired true false) =
  false.
Proof.
  unfold bond_forming_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_bond_forming_bundle_refuse :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — bond-forming refuse                *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false true =
  verdict_proved_without_bar_refuse /\
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_bundle
       bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
       bondClaimFormingBarAbsent false false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold bond_forming_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — bond-forming lattice not production wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_proved false true) =
  false.
Proof.
  unfold bond_forming_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Bond-forming **conservation** coherence scaffold                    *)
(* ------------------------------------------------------------------ *)

Definition bond_forming_conservation_coherence_scaffold : bool :=
  bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_proved false false) &&
  negb (bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_unwired true false)) &&
  negb (bond_forming_conservation_verdict_ok
    (evaluate_bond_forming_conservation_close
       bond_forming_conservation_proved false true)).

Lemma bond_forming_conservation_coherence_scaffold_true :
  bond_forming_conservation_coherence_scaffold = true.
Proof.
  unfold bond_forming_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem bond_forming_conservation_coherence_scaffold_theorem :
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_proved false false =
    verdict_bond_forming_named_ok /\
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_proved false true =
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

Definition bond_forming_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition bond_forming_conservation_knowing_fiber_ok : bool :=
  bond_forming_conservation_fiber_ok fiber_quantum_knowing.

Definition bond_forming_conservation_meso_acting_ok : bool :=
  bond_forming_conservation_fiber_ok fiber_meso_acting.

Lemma bond_forming_conservation_knowing_fiber_ok_true :
  bond_forming_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma bond_forming_conservation_meso_acting_not_ok :
  bond_forming_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem bond_forming_conservation_routes_knowing_not_meso :
  bond_forming_conservation_knowing_fiber_ok = true /\
  bond_forming_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply bond_forming_conservation_knowing_fiber_ok_true.
  - apply bond_forming_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  bond_forming_conservation_knowing_fiber_ok &&
  negb bond_forming_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, bond_forming_conservation_knowing_fiber_ok,
    bond_forming_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named bond-forming + fail-closed + fiber          *)
(* ------------------------------------------------------------------ *)

Theorem bond_forming_conservation_fixture_scaffold :
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false false =
    verdict_bond_forming_named_ok /\
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleEmptyWitness
    bondClaimFormingBarAbsent false false false false =
    verdict_trivial_bundle_refuse /\
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent true false false false =
    verdict_xor_classifier_refuse /\
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false true false false =
    verdict_refine_forming_refuse /\
  evaluate_bond_forming_bundle
    bond_forming_conservation_unwired patternBundleBondFormingSharedWitness
    bondClaimFormingBarAbsent false false false true =
    verdict_proved_without_bar_refuse /\
  evaluate_bond_forming_conservation_close
    bond_forming_conservation_unwired false false =
    verdict_unwired_ok /\
  bond_forming_conservation_knowing_fiber_ok = true /\
  bond_forming_conservation_meso_acting_ok = false /\
  bondFormingProved = false /\
  productNotXor = true /\
  formingArrowIsInteractNotRefine = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — bond-forming)        *)
(* ------------------------------------------------------------------ *)

Definition bondFormingConservationAuthority : string :=
  "umst/umst-chem/src/x_rows/bond_forming_conservation.rs".

Definition bondFormingTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/bond_forming.rs".

Definition patternTaxonomyAuthority : string :=
  "umst/umst-chem/src/pattern_taxonomy.rs".

Definition chemL0Pattern00Authority : string :=
  "CHEM-L0-PATTERN-00".

Definition chemIntPatternBundleProductAuthority : string :=
  "CHEM-INT-PATTERN-BUNDLE-PRODUCT".

Definition qtaimBcpMayerDdecAuthority : string :=
  "QTAIM BCP + Mayer/DDEC — bond-topology witness named; not second axiom".

Definition bondFormingConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-BOND-FORMING-CONSERVATION".

Definition bondFormingConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-BOND-FORMING-CONSERVATION class 2 Bond-forming QTAIM BCP Mayer DDEC concurrent Pi_c identity conserved cardinality 25 present product not XOR XOR mutually exclusive refuse forming arrow Kleisli Interact Apply not Refine bond_forming shared nuance witness concurrent bondFormingProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second bond-forming axiom not GREEN DFT not physics GREEN not production_wired".

Lemma bond_forming_conservation_cell_id :
  bondFormingConservationCellId =
  "CHEM-FORMAL-Q-COQ-BOND-FORMING-CONSERVATION".
Proof. reflexivity. Qed.

Lemma bond_forming_conservation_cites_int_bond_forming_conservation_rs :
  bondFormingConservationAuthority <>
  "".
Proof. discriminate. Qed.

Lemma bond_forming_conservation_authority_path :
  bondFormingConservationAuthority =
  "umst/umst-chem/src/x_rows/bond_forming_conservation.rs".
Proof. reflexivity. Qed.

Lemma bond_forming_conservation_cites_l0_pattern_00 :
  chemL0Pattern00Authority = "CHEM-L0-PATTERN-00".
Proof. reflexivity. Qed.

Lemma bond_forming_conservation_cites_int_pattern_bundle_product :
  chemIntPatternBundleProductAuthority = "CHEM-INT-PATTERN-BUNDLE-PRODUCT".
Proof. reflexivity. Qed.

Lemma bond_forming_conservation_cites_qtaim_bcp :
  qtaimBcpMayerDdecAuthority <> "".
Proof. discriminate. Qed.

Lemma bond_forming_conservation_cites_marker :
  concurrentProductMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not second axiom  *)
(* ------------------------------------------------------------------ *)

Definition bondFormingSecondLawConservationFraming : string :=
  "second_law_conservation_bond_forming_one_axiom_not_second_bond_forming_axiom".

Lemma bond_forming_not_second_axiom :
  bondFormingSecondLawConservationFraming <> "second_bond_forming_axiom".
Proof. discriminate. Qed.

Lemma bond_forming_second_law_conservation_framing :
  bondFormingSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma bond_forming_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma bond_forming_conservation_modality_unwired :
  bondFormingConservationModalityCurrent = bond_forming_conservation_unwired.
Proof. reflexivity. Qed.

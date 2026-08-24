(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: SharedConservation.v                                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: PATTERN-00 pattern class 1 **shared**           *)
(*  **conservation**. CEF sublattice + QTAIM bond paths + CAT-02       *)
(*  pullback; shared sites are neighbors not independent SpeciesId;     *)
(*  concurrent Π_c identity conserved (cardinality 25; ≥2 Present slots *)
(*  is **product**, not XOR). XOR mutually-exclusive classifiers refuse; *)
(*  per_element_nuance + shared concurrent witness. Trivial empty-bundle *)
(*  fail-closed; GREEN invent fail-closed; Proved-without-bar fail-closed. *)
(*  Geometry routes knowing/quantum fiber not meso acting. Not 118² GREEN. *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — shared class factor is not a second      *)
(*  axiom. Cites PatternProductConservation + INT shared_conservation. *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 class 1 **shared** **conservation** modality             *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive SharedConservationModality : Type :=
  | shared_conservation_unwired
  | shared_conservation_assumed
  | shared_conservation_proved
  | shared_conservation_surrogate.

Definition sharedConservationModalityCurrent : SharedConservationModality :=
  shared_conservation_unwired.

Definition shared_lattice_cardinality : nat := 4.

Lemma shared_lattice_cardinality_is_four :
  shared_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma shared_lattice_not_118_squared :
  negb (Nat.eqb shared_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold shared_lattice_cardinality.
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

Definition pattern_class_per_element_nuance_idx : nat := 0.
Definition pattern_class_shared_idx : nat := 1.

Lemma pattern_class_per_element_nuance_idx_is_0 :
  pattern_class_per_element_nuance_idx = 0.
Proof. reflexivity. Qed.

Lemma pattern_class_shared_idx_is_1 :
  pattern_class_shared_idx = 1.
Proof. reflexivity. Qed.

Lemma pattern_class_shared_indices_valid :
  pattern_class_index_valid pattern_class_per_element_nuance_idx = true /\
  pattern_class_index_valid pattern_class_shared_idx = true.
Proof.
  repeat split; unfold pattern_class_index_valid, pattern_class_cardinality;
  reflexivity.
Qed.

Definition northStarClass1SharedTag : string := "class 1 shared".

Lemma north_star_class_1_shared_tag_named :
  northStarClass1SharedTag = "class 1 shared".
Proof. reflexivity. Qed.

Definition patternClassSharedTag : string := "shared".

Lemma pattern_class_shared_tag_named :
  patternClassSharedTag = "shared".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  CEF / QTAIM / CAT-02 pullback scaffold — shared site physics pins   *)
(* ------------------------------------------------------------------ *)

Definition cefSublatticeAuthority : string :=
  "umst/umst-chem/src/cef_sublattice_is_not_species.rs".

Definition qtaimBondPathAuthority : string :=
  "umst/umst-chem/src/l0_tables/shared.rs".

Definition cat02PullbackAuthority : string :=
  "umst/umst-chem/src/shared_substructure_limits.rs".

Definition chemIntCefSublatticeNotSpeciesCellId : string :=
  "CHEM-INT-CEF-SUBLATTICE-NOT-SPECIES".

Definition chemL0Cat02CellId : string :=
  "CHEM-L0-CAT-02".

Definition chemIntNuanceSharedCellId : string :=
  "CHEM-INT-NUANCE-SHARED".

Lemma cef_sublattice_authority_cited :
  cefSublatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma qtaim_bond_path_authority_cited :
  qtaimBondPathAuthority <> "".
Proof. discriminate. Qed.

Lemma cat02_pullback_authority_cited :
  cat02PullbackAuthority <> "".
Proof. discriminate. Qed.

Lemma cef_sublattice_not_species_cell_named :
  chemIntCefSublatticeNotSpeciesCellId =
  "CHEM-INT-CEF-SUBLATTICE-NOT-SPECIES".
Proof. reflexivity. Qed.

Lemma cat02_cell_named :
  chemL0Cat02CellId = "CHEM-L0-CAT-02".
Proof. reflexivity. Qed.

Definition sharedSiteNeSpeciesIdCollision : string :=
  "shared site is neighbor not independent SpeciesId tag".

Definition parallelSharedAxiomNeTableCollision : string :=
  "parallel shared axiom not Z-keyed shared nuance table".

Lemma shared_site_ne_species_id_collision_named :
  sharedSiteNeSpeciesIdCollision <> "".
Proof. discriminate. Qed.

Lemma parallel_shared_axiom_ne_table_collision_named :
  parallelSharedAxiomNeTableCollision <> "".
Proof. discriminate. Qed.

Definition sharedSiteNotIndependentSpeciesId : bool := true.

Lemma shared_site_not_independent_species_id :
  sharedSiteNotIndependentSpeciesId = true.
Proof. reflexivity. Qed.

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

Definition patternBundleAbsentSlot : pattern_bundle_slot := bundle_slot_absent.

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

(* Shared concurrent witness: class 0 per_element_nuance + class 1 shared. *)
Definition patternBundleSharedConcurrentWitness : pattern_bundle :=
  patternBundleWithPresent
    (patternBundleWithPresent patternBundleAllUnwired
      pattern_class_per_element_nuance_idx)
    pattern_class_shared_idx.

Definition patternBundleEmptyWitness : pattern_bundle :=
  patternBundleAllUnwired.

Definition patternBundleSingleShared : pattern_bundle :=
  patternBundleWithPresent patternBundleAllUnwired pattern_class_shared_idx.

Lemma shared_concurrent_per_element_nuance_present :
  patternBundleHolds patternBundleSharedConcurrentWitness
    pattern_class_per_element_nuance_idx = true.
Proof. reflexivity. Qed.

Lemma shared_concurrent_shared_present :
  patternBundleHolds patternBundleSharedConcurrentWitness
    pattern_class_shared_idx = true.
Proof. reflexivity. Qed.

Lemma shared_concurrent_present_count_is_two :
  patternBundlePresentCount patternBundleSharedConcurrentWitness = 2.
Proof. reflexivity. Qed.

Lemma shared_concurrent_is_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleSharedConcurrentWitness = true.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite shared_concurrent_present_count_is_two.
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

Lemma single_shared_present_count_is_one :
  patternBundlePresentCount patternBundleSingleShared = 1.
Proof. reflexivity. Qed.

Lemma single_shared_not_concurrent_product :
  patternBundleIsConcurrentProduct patternBundleSingleShared = false.
Proof.
  unfold patternBundleIsConcurrentProduct.
  rewrite single_shared_present_count_is_one.
  reflexivity.
Qed.

Lemma shared_concurrent_identity_conserved :
  patternBundleIdentityConserved patternBundleSharedConcurrentWitness
    patternBundleSharedConcurrentWitness = true.
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

Lemma xor_refuse_on_shared_concurrent :
  xorClassifierIncompatible true patternBundleSharedConcurrentWitness = true.
Proof.
  unfold xorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma xor_ok_on_concurrent_product_claim :
  xorClassifierIncompatible false patternBundleSharedConcurrentWitness = false.
Proof. reflexivity. Qed.

Definition sharedNotXor : bool :=
  patternBundleIsConcurrentProduct patternBundleSharedConcurrentWitness &&
  xorClassifierIncompatible true patternBundleSharedConcurrentWitness.

Lemma shared_not_xor_true : sharedNotXor = true.
Proof.
  unfold sharedNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_shared_not_xor :
  sharedNotXor = true /\
  Nat.leb 2 (patternBundlePresentCount patternBundleSharedConcurrentWitness) = true /\
  xorClassifierMarker <> concurrentProductMarker.
Proof.
  split.
  - apply shared_not_xor_true.
  - split.
    + rewrite shared_concurrent_present_count_is_two.
      reflexivity.
    + apply xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Shared bar — Proved-without-bar fail-closed                         *)
(* ------------------------------------------------------------------ *)

Inductive shared_bar_presence : Type :=
  | shared_bar_absent
  | shared_bar_present.

Record shared_claim_bar : Type := {
  shared_bar_presence_tag : shared_bar_presence;
  shared_bar_defect_total : nat
}.

Definition sharedClaimBarAbsent : shared_claim_bar :=
  {| shared_bar_presence_tag := shared_bar_absent;
     shared_bar_defect_total := 0 |}.

Definition sharedClaimBarZeroDefect : shared_claim_bar :=
  {| shared_bar_presence_tag := shared_bar_present;
     shared_bar_defect_total := 0 |}.

Definition shared_claim_bar_zero_defect (b : shared_claim_bar) : bool :=
  match shared_bar_presence_tag b with
  | shared_bar_absent => false
  | shared_bar_present =>
      Nat.eqb (shared_bar_defect_total b) 0
  end.

Lemma shared_claim_bar_zero_defect_true :
  shared_claim_bar_zero_defect sharedClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma shared_claim_bar_absent_not_zero_defect :
  shared_claim_bar_zero_defect sharedClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Shared **conservation** verdict — fail-closed lattice               *)
(* ------------------------------------------------------------------ *)

Inductive shared_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_shared_named_ok
  | verdict_trivial_bundle_refuse
  | verdict_xor_classifier_refuse
  | verdict_species_id_independent_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition shared_conservation_verdict_ok
  (v : shared_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_shared_named_ok => true
  | _ => false
  end.

Definition patternBundleNontrivial (b : pattern_bundle) : bool :=
  Nat.ltb 0 (patternBundlePresentCount b).

Definition evaluate_shared_bundle
  (m : SharedConservationModality)
  (b : pattern_bundle)
  (bar : shared_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_species_id_independent : bool) : shared_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_species_id_independent
            then verdict_species_id_independent_refuse
            else if negb (patternBundleNontrivial b)
                 then verdict_trivial_bundle_refuse
                 else if xorClassifierIncompatible claim_xor_classifier b
                      then verdict_xor_classifier_refuse
                      else
                        match m with
                        | shared_conservation_unwired => verdict_shared_named_ok
                        | shared_conservation_assumed
                        | shared_conservation_surrogate => verdict_unwired_ok
                        | shared_conservation_proved =>
                            verdict_proved_without_bar_refuse
                        end.

Definition evaluate_shared_conservation_close
  (m : SharedConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : shared_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | shared_conservation_unwired => verdict_unwired_ok
    | shared_conservation_assumed
    | shared_conservation_proved
    | shared_conservation_surrogate => verdict_shared_named_ok
    end.

Definition shared_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_shared_conservation_close
          shared_conservation_proved claim_physics_green claim_production_wired with
  | verdict_shared_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Shared **conservation** law cells — four laws, Unwired              *)
(* ------------------------------------------------------------------ *)

Inductive shared_conservation_law : Type :=
  | law_shared_named
  | law_xor_classifier_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition shared_conservation_law_count : nat := 4.

Lemma shared_conservation_law_count_is_four :
  shared_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive shared_conservation_law_witness : Type :=
  | shared_law_witness_open
  | shared_law_witness_proved.

Definition evaluate_shared_conservation_law_witness
  (law : shared_conservation_law) (m : SharedConservationModality)
  : shared_conservation_law_witness :=
  match m with
  | shared_conservation_unwired
  | shared_conservation_assumed
  | shared_conservation_surrogate => shared_law_witness_open
  | shared_conservation_proved => shared_law_witness_proved
  end.

Lemma all_shared_conservation_laws_open_at_unwired :
  evaluate_shared_conservation_law_witness law_shared_named
    shared_conservation_unwired = shared_law_witness_open /\
  evaluate_shared_conservation_law_witness law_xor_classifier_refuse
    shared_conservation_unwired = shared_law_witness_open /\
  evaluate_shared_conservation_law_witness law_green_invent_refuse
    shared_conservation_unwired = shared_law_witness_open /\
  evaluate_shared_conservation_law_witness law_production_wired_refuse
    shared_conservation_unwired = shared_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PATTERN-00 pins (structure witnesses — shared laws not Proved)      *)
(* ------------------------------------------------------------------ *)

Definition pattern00SharedProved : bool := false.

Lemma pattern00_shared_proved_false : pattern00SharedProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

Definition cat02PullbackProved : bool := false.

Lemma cat02_pullback_not_proved : cat02PullbackProved = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_shared_conservation_close
    shared_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_shared_conservation_close
    shared_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_unwired false false) =
  true.
Proof.
  unfold shared_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named shared concurrent close — Π_c **conservation**              *)
(* ------------------------------------------------------------------ *)

Lemma shared_concurrent_named_ok :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false false =
  verdict_shared_named_ok.
Proof. reflexivity. Qed.

Theorem named_shared_concurrent_conservation :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false false =
  verdict_shared_named_ok /\
  patternBundleIdentityConserved patternBundleSharedConcurrentWitness
    patternBundleSharedConcurrentWitness = true /\
  patternBundleIsConcurrentProduct patternBundleSharedConcurrentWitness = true /\
  patternBundleHolds patternBundleSharedConcurrentWitness pattern_class_shared_idx = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma shared_named_close_ok :
  evaluate_shared_conservation_close
    shared_conservation_proved false false =
  verdict_shared_named_ok.
Proof. reflexivity. Qed.

Theorem named_shared_conservation_close :
  evaluate_shared_conservation_close
    shared_conservation_proved false false =
  verdict_shared_named_ok /\
  shared_conservation_authorized false false = true.
Proof.
  split.
  - apply shared_named_close_ok.
  - unfold shared_conservation_authorized.
    rewrite shared_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — shared **conservation** refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleEmptyWitness
    sharedClaimBarAbsent false false false false =
  verdict_trivial_bundle_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleEmptyWitness
    sharedClaimBarAbsent false false false false =
  verdict_trivial_bundle_refuse /\
  shared_conservation_verdict_ok
    (evaluate_shared_bundle
       shared_conservation_unwired patternBundleEmptyWitness
       sharedClaimBarAbsent false false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold shared_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse            *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent true false false false =
  verdict_xor_classifier_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent true false false false =
  verdict_xor_classifier_refuse /\
  shared_conservation_verdict_ok
    (evaluate_shared_bundle
       shared_conservation_unwired patternBundleSharedConcurrentWitness
       sharedClaimBarAbsent true false false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold shared_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId independent refuse — shared site neighbor not SpeciesId   *)
(* ------------------------------------------------------------------ *)

Lemma species_id_independent_refused :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false true =
  verdict_species_id_independent_refuse.
Proof. reflexivity. Qed.

Theorem species_id_independent_fail_closed :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false true =
  verdict_species_id_independent_refuse /\
  shared_conservation_verdict_ok
    (evaluate_shared_bundle
       shared_conservation_unwired patternBundleSharedConcurrentWitness
       sharedClaimBarAbsent false false false true) =
  false.
Proof.
  split.
  - apply species_id_independent_refused.
  - unfold shared_conservation_verdict_ok.
    rewrite species_id_independent_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_shared_conservation_close
    shared_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_unwired true false) =
  false.
Proof.
  unfold shared_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_shared_bundle_refuse :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false true false false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — shared **conservation** refuse    *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false true false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false true false =
  verdict_proved_without_bar_refuse /\
  shared_conservation_verdict_ok
    (evaluate_shared_bundle
       shared_conservation_unwired patternBundleSharedConcurrentWitness
       sharedClaimBarAbsent false false true false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold shared_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — shared lattice not production wired       *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_shared_conservation_close
    shared_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_proved false true) =
  false.
Proof.
  unfold shared_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Shared **conservation** coherence scaffold                          *)
(* ------------------------------------------------------------------ *)

Definition shared_conservation_coherence_scaffold : bool :=
  shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_proved false false) &&
  negb (shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_unwired true false)) &&
  negb (shared_conservation_verdict_ok
    (evaluate_shared_conservation_close
       shared_conservation_proved false true)).

Lemma shared_conservation_coherence_scaffold_true :
  shared_conservation_coherence_scaffold = true.
Proof.
  unfold shared_conservation_coherence_scaffold, shared_conservation_verdict_ok.
  simpl.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_shared_conservation.

Definition shared_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition shared_conservation_knowing_fiber_ok : bool :=
  shared_conservation_fiber_ok fiber_quantum_knowing.

Definition shared_conservation_meso_acting_ok : bool :=
  shared_conservation_fiber_ok fiber_meso_acting.

Lemma shared_conservation_knowing_fiber_ok_true :
  shared_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma shared_conservation_meso_acting_not_ok :
  shared_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem shared_conservation_routes_knowing_not_meso :
  shared_conservation_knowing_fiber_ok = true /\
  shared_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply shared_conservation_knowing_fiber_ok_true.
  - apply shared_conservation_meso_acting_not_ok.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named shared + fail-closed + fiber + class 1     *)
(* ------------------------------------------------------------------ *)

Theorem shared_conservation_fixture_scaffold :
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false false =
    verdict_shared_named_ok /\
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleEmptyWitness
    sharedClaimBarAbsent false false false false =
    verdict_trivial_bundle_refuse /\
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent true false false false =
    verdict_xor_classifier_refuse /\
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false true false =
    verdict_proved_without_bar_refuse /\
  evaluate_shared_bundle
    shared_conservation_unwired patternBundleSharedConcurrentWitness
    sharedClaimBarAbsent false false false true =
    verdict_species_id_independent_refuse /\
  evaluate_shared_conservation_close
    shared_conservation_unwired false false =
    verdict_unwired_ok /\
  shared_conservation_knowing_fiber_ok = true /\
  shared_conservation_meso_acting_ok = false /\
  pattern00SharedProved = false /\
  sharedNotXor = true /\
  sharedSiteNotIndependentSpeciesId = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — shared class 1)      *)
(* ------------------------------------------------------------------ *)

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition sharedConservationIntAuthority : string :=
  "umst/umst-chem/src/x_rows/shared_conservation.rs".

Definition patternTaxonomyAuthority : string :=
  "umst/umst-chem/src/pattern_taxonomy.rs".

Definition chemL0Pattern00Authority : string :=
  "CHEM-L0-PATTERN-00".

Definition chemIntPatternBundleProductAuthority : string :=
  "CHEM-INT-PATTERN-BUNDLE-PRODUCT".

Definition chemIntCrossSharedConservationAuthority : string :=
  "CHEM-INT-CROSS-SHARED-CONSERVATION".

Definition sharedConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-SHARED-CONSERVATION".

Definition sharedConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-SHARED-CONSERVATION PATTERN-00 pattern class 1 shared conservation CEF sublattice QTAIM bond paths CAT-02 pullback shared sites neighbor not independent SpeciesId concurrent Pi_c identity conserved cardinality 25 present slots product not XOR xor mutually exclusive classifiers refuse per_element_nuance shared concurrent witness trivial empty bundle fail-closed GREEN invent fail-closed proved-without-bar fail-closed pattern00SharedProved false cat02PullbackProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second shared axiom not GREEN DFT not physics GREEN not production_wired".

Lemma shared_conservation_cell_id :
  sharedConservationCellId = "CHEM-FORMAL-Q-COQ-SHARED-CONSERVATION".
Proof. reflexivity. Qed.

Lemma shared_cites_pattern_product_conservation_v :
  patternProductConservationAuthority <>
  "".
Proof. discriminate. Qed.

Lemma shared_cites_int_shared_conservation_rs :
  sharedConservationIntAuthority <>
  "".
Proof. discriminate. Qed.

Lemma shared_cites_pattern_taxonomy_rs :
  patternTaxonomyAuthority <> "".
Proof. discriminate. Qed.

Lemma shared_cites_l0_pattern_00 :
  chemL0Pattern00Authority = "CHEM-L0-PATTERN-00".
Proof. reflexivity. Qed.

Lemma shared_cites_int_pattern_bundle_product :
  chemIntPatternBundleProductAuthority = "CHEM-INT-PATTERN-BUNDLE-PRODUCT".
Proof. reflexivity. Qed.

Lemma shared_cites_int_cross_shared_conservation :
  chemIntCrossSharedConservationAuthority =
  "CHEM-INT-CROSS-SHARED-CONSERVATION".
Proof. reflexivity. Qed.

Lemma shared_cites_concurrent_product_marker :
  concurrentProductMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not second shared *)
(* ------------------------------------------------------------------ *)

Definition sharedSecondLawConservationFraming : string :=
  "second_law_conservation_shared_one_axiom_not_second_shared_axiom".

Lemma shared_not_second_shared_axiom :
  sharedSecondLawConservationFraming <> "second_shared_axiom".
Proof. discriminate. Qed.

Lemma shared_second_law_conservation_framing :
  sharedSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma shared_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma shared_conservation_modality_unwired :
  sharedConservationModalityCurrent = shared_conservation_unwired.
Proof. reflexivity. Qed.

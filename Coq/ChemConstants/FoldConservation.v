(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: FoldConservation.v                                    *)
(*                                                                      *)
(*  Knowing-fiber Coq: FP-01 classifier-fold conservation. Pattern     *)
(*  taxonomy classifiers as predicates with conjunctive / disjunctive  *)
(*  fold combinators; empty-fold identity conserved. Modality Unwired;   *)
(*  fp01FoldProved Unwired not Proved. Geometry routes knowing/quantum   *)
(*  fiber not meso acting. Not 118² GREEN table.                         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — fold conservation is not a second axiom.      *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  FP-01 classifier-fold conservation modality (Unwired / Assumed /    *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive FoldConservationModality : Type :=
  | fold_conservation_unwired
  | fold_conservation_assumed
  | fold_conservation_proved
  | fold_conservation_surrogate.

Definition foldConservationModalityCurrent : FoldConservationModality :=
  fold_conservation_unwired.

Definition fold_lattice_cardinality : nat := 4.

Lemma fold_lattice_cardinality_is_four :
  fold_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma fold_lattice_not_118_squared :
  negb (Nat.eqb fold_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold fold_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  PatternFeature snapshot — §2 taxonomy classifier scaffold           *)
(* ------------------------------------------------------------------ *)

Record pattern_feature : Type := {
  feature_per_element : bool;
  feature_shared : bool;
  feature_bond_forming : bool;
  feature_bond_repelling : bool;
  feature_structure_enabling : bool;
  feature_structure_blocking : bool
}.

Definition patternFeatureZero : pattern_feature :=
  {| feature_per_element := false;
     feature_shared := false;
     feature_bond_forming := false;
     feature_bond_repelling := false;
     feature_structure_enabling := false;
     feature_structure_blocking := false |}.

Definition patternFeatureBondForming : pattern_feature :=
  {| feature_per_element := false;
     feature_shared := false;
     feature_bond_forming := true;
     feature_bond_repelling := false;
     feature_structure_enabling := false;
     feature_structure_blocking := false |}.

(* ------------------------------------------------------------------ *)
(*  PatternClassifierKind — pure bool classifiers on features           *)
(* ------------------------------------------------------------------ *)

Inductive pattern_classifier_kind : Type :=
  | pc_per_element
  | pc_shared
  | pc_bond_forming
  | pc_bond_repelling
  | pc_structure_enabling
  | pc_structure_blocking.

Definition classify (k : pattern_classifier_kind) (f : pattern_feature) : bool :=
  match k with
  | pc_per_element => f.(feature_per_element)
  | pc_shared => f.(feature_shared)
  | pc_bond_forming => f.(feature_bond_forming)
  | pc_bond_repelling => f.(feature_bond_repelling)
  | pc_structure_enabling => f.(feature_structure_enabling)
  | pc_structure_blocking => f.(feature_structure_blocking)
  end.

Lemma classify_bond_forming_on_bond_features :
  classify pc_bond_forming patternFeatureBondForming = true.
Proof. reflexivity. Qed.

Lemma classify_structure_enabling_on_bond_features :
  classify pc_structure_enabling patternFeatureBondForming = false.
Proof. reflexivity. Qed.

Lemma classify_pure_bool_bond_forming :
  classify pc_bond_forming patternFeatureBondForming =
  patternFeatureBondForming.(feature_bond_forming).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ClassifierFoldOp — conjunctive / disjunctive fold combinator        *)
(* ------------------------------------------------------------------ *)

Inductive classifier_fold_op : Type :=
  | fold_conjunctive
  | fold_disjunctive.

Fixpoint fold_classifiers_step
  (kinds : list pattern_classifier_kind)
  (op : classifier_fold_op)
  (features : pattern_feature)
  (acc : bool) : bool :=
  match kinds with
  | nil => acc
  | k :: rest =>
      let next := classify k features in
      let combined :=
        match op with
        | fold_conjunctive => acc && next
        | fold_disjunctive => acc || next
        end in
      fold_classifiers_step rest op features combined
  end.

Definition fold_classifiers
  (kinds : list pattern_classifier_kind)
  (op : classifier_fold_op)
  (features : pattern_feature) : bool :=
  match kinds with
  | nil =>
      match op with
      | fold_conjunctive => true
      | fold_disjunctive => false
      end
  | k :: rest =>
      fold_classifiers_step rest op features (classify k features)
  end.

Definition manual_conjunctive_fold
  (k1 k2 : pattern_classifier_kind) (f : pattern_feature) : bool :=
  classify k1 f && classify k2 f.

Definition manual_disjunctive_fold
  (k1 k2 : pattern_classifier_kind) (f : pattern_feature) : bool :=
  classify k1 f || classify k2 f.

Definition bond_forming_structure_enabling_kinds : list pattern_classifier_kind :=
  [pc_bond_forming; pc_structure_enabling].

(* ------------------------------------------------------------------ *)
(*  Empty-fold identity — conjunctive true, disjunctive false           *)
(* ------------------------------------------------------------------ *)

Lemma conjunctive_empty_fold_identity :
  fold_classifiers [] fold_conjunctive patternFeatureZero = true.
Proof. reflexivity. Qed.

Lemma disjunctive_empty_fold_identity :
  fold_classifiers [] fold_disjunctive patternFeatureZero = false.
Proof. reflexivity. Qed.

Theorem conjunctive_empty_fold_identity_conserved :
  fold_classifiers [] fold_conjunctive patternFeatureBondForming = true.
Proof. reflexivity. Qed.

Theorem disjunctive_empty_fold_identity_conserved :
  fold_classifiers [] fold_disjunctive patternFeatureBondForming = false.
Proof. reflexivity. Qed.

Lemma conjunctive_empty_identity_on_any_feature (f : pattern_feature) :
  fold_classifiers [] fold_conjunctive f = true.
Proof.
  destruct f; reflexivity.
Qed.

Lemma disjunctive_empty_identity_on_any_feature (f : pattern_feature) :
  fold_classifiers [] fold_disjunctive f = false.
Proof.
  destruct f; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Conjunctive / disjunctive fold identity conserved (lemmas)          *)
(* ------------------------------------------------------------------ *)

Lemma conjunctive_fold_identity_conserved :
  fold_classifiers bond_forming_structure_enabling_kinds fold_conjunctive
    patternFeatureBondForming =
  manual_conjunctive_fold pc_bond_forming pc_structure_enabling
    patternFeatureBondForming.
Proof. reflexivity. Qed.

Lemma disjunctive_fold_identity_conserved :
  fold_classifiers bond_forming_structure_enabling_kinds fold_disjunctive
    patternFeatureBondForming =
  manual_disjunctive_fold pc_bond_forming pc_structure_enabling
    patternFeatureBondForming.
Proof. reflexivity. Qed.

Theorem conjunctive_fold_conservation :
  fold_classifiers bond_forming_structure_enabling_kinds fold_conjunctive
    patternFeatureBondForming =
  classify pc_bond_forming patternFeatureBondForming &&
  classify pc_structure_enabling patternFeatureBondForming.
Proof.
  rewrite conjunctive_fold_identity_conserved.
  unfold manual_conjunctive_fold.
  reflexivity.
Qed.

Theorem disjunctive_fold_conservation :
  fold_classifiers bond_forming_structure_enabling_kinds fold_disjunctive
    patternFeatureBondForming =
  classify pc_bond_forming patternFeatureBondForming ||
  classify pc_structure_enabling patternFeatureBondForming.
Proof.
  rewrite disjunctive_fold_identity_conserved.
  unfold manual_disjunctive_fold.
  reflexivity.
Qed.

Lemma conjunctive_fold_bond_features_false :
  fold_classifiers bond_forming_structure_enabling_kinds fold_conjunctive
    patternFeatureBondForming = false.
Proof.
  rewrite conjunctive_fold_conservation.
  rewrite classify_bond_forming_on_bond_features.
  rewrite classify_structure_enabling_on_bond_features.
  reflexivity.
Qed.

Lemma disjunctive_fold_bond_features_true :
  fold_classifiers bond_forming_structure_enabling_kinds fold_disjunctive
    patternFeatureBondForming = true.
Proof.
  rewrite disjunctive_fold_conservation.
  rewrite classify_bond_forming_on_bond_features.
  rewrite classify_structure_enabling_on_bond_features.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fold conservation close verdict — fail-closed lattice               *)
(* ------------------------------------------------------------------ *)

Inductive fold_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_conjunctive_fold_ok
  | verdict_disjunctive_fold_ok
  | verdict_green_invent_refuse
  | verdict_production_wired_refuse.

Definition fold_conservation_verdict_ok (v : fold_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_conjunctive_fold_ok => true
  | verdict_disjunctive_fold_ok => true
  | _ => false
  end.

Definition fold_conservation_verdict_beq
  (v1 v2 : fold_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_conjunctive_fold_ok, verdict_conjunctive_fold_ok => true
  | verdict_disjunctive_fold_ok, verdict_disjunctive_fold_ok => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_fold_conservation_close
  (m : FoldConservationModality)
  (op : classifier_fold_op)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : fold_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | fold_conservation_unwired => verdict_unwired_ok
    | fold_conservation_assumed
    | fold_conservation_proved
    | fold_conservation_surrogate =>
        match op with
        | fold_conjunctive => verdict_conjunctive_fold_ok
        | fold_disjunctive => verdict_disjunctive_fold_ok
        end
    end.

Definition fold_conservation_authorized
  (op : classifier_fold_op)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_fold_conservation_close
          fold_conservation_proved op claim_physics_green claim_production_wired with
  | verdict_conjunctive_fold_ok => true
  | verdict_disjunctive_fold_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Fold conservation law cells — four laws, open @ Unwired             *)
(* ------------------------------------------------------------------ *)

Inductive fold_conservation_law : Type :=
  | law_conjunctive_fold_identity
  | law_disjunctive_fold_identity
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition fold_conservation_law_count : nat := 4.

Lemma fold_conservation_law_count_is_four :
  fold_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive fold_conservation_law_witness : Type :=
  | fold_law_witness_open
  | fold_law_witness_proved.

Definition evaluate_fold_conservation_law_witness
  (law : fold_conservation_law) (m : FoldConservationModality)
  : fold_conservation_law_witness :=
  match m with
  | fold_conservation_unwired
  | fold_conservation_assumed
  | fold_conservation_surrogate => fold_law_witness_open
  | fold_conservation_proved => fold_law_witness_proved
  end.

Lemma all_fold_conservation_laws_open_at_unwired :
  evaluate_fold_conservation_law_witness law_conjunctive_fold_identity
    fold_conservation_unwired = fold_law_witness_open /\
  evaluate_fold_conservation_law_witness law_disjunctive_fold_identity
    fold_conservation_unwired = fold_law_witness_open /\
  evaluate_fold_conservation_law_witness law_green_invent_refuse
    fold_conservation_unwired = fold_law_witness_open /\
  evaluate_fold_conservation_law_witness law_production_wired_refuse
    fold_conservation_unwired = fold_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  FP-01 pins (structure witnesses — fold laws not Proved)           *)
(* ------------------------------------------------------------------ *)

Definition fp01FoldProved : bool := false.

Lemma fp01_fold_proved_false : fp01FoldProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_fold_conservation_close
    fold_conservation_unwired fold_conjunctive false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_fold_conservation_close
    fold_conservation_unwired fold_conjunctive false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_unwired fold_conjunctive false false) =
  true.
Proof.
  unfold fold_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Conjunctive fold close — classifier fold identity conserved         *)
(* ------------------------------------------------------------------ *)

Lemma conjunctive_fold_close_ok :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_conjunctive false false =
  verdict_conjunctive_fold_ok.
Proof. reflexivity. Qed.

Theorem classifier_conjunctive_fold_conservation_close :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_conjunctive false false =
  verdict_conjunctive_fold_ok /\
  fold_conservation_authorized fold_conjunctive false false = true.
Proof.
  split.
  - apply conjunctive_fold_close_ok.
  - unfold fold_conservation_authorized.
    rewrite conjunctive_fold_close_ok.
    reflexivity.
Qed.

Lemma conjunctive_fold_verdict_ok :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_conjunctive false false) =
  true.
Proof.
  unfold fold_conservation_verdict_ok.
  rewrite conjunctive_fold_close_ok.
  reflexivity.
Qed.

Lemma conjunctive_fold_still_not_fp01_proved :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_conjunctive false false) =
  true /\
  fp01FoldProved = false.
Proof.
  split.
  - apply conjunctive_fold_verdict_ok.
  - apply fp01_fold_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Disjunctive fold close — classifier fold identity conserved         *)
(* ------------------------------------------------------------------ *)

Lemma disjunctive_fold_close_ok :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_disjunctive false false =
  verdict_disjunctive_fold_ok.
Proof. reflexivity. Qed.

Theorem classifier_disjunctive_fold_conservation_close :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_disjunctive false false =
  verdict_disjunctive_fold_ok /\
  fold_conservation_authorized fold_disjunctive false false = true.
Proof.
  split.
  - apply disjunctive_fold_close_ok.
  - unfold fold_conservation_authorized.
    rewrite disjunctive_fold_close_ok.
    reflexivity.
Qed.

Lemma disjunctive_fold_verdict_ok :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_disjunctive false false) =
  true.
Proof.
  unfold fold_conservation_verdict_ok.
  rewrite disjunctive_fold_close_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_fold_conservation_close
    fold_conservation_unwired fold_conjunctive true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_unwired fold_conjunctive true false) =
  false.
Proof.
  unfold fold_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — classifier folds not production wired   *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_conjunctive false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  fold_conservation_verdict_ok
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_conjunctive false true) =
  false.
Proof.
  unfold fold_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fold conservation coherence scaffold — fixture witnesses            *)
(* ------------------------------------------------------------------ *)

Definition fold_conservation_coherence_scaffold : bool :=
  fold_conservation_verdict_beq
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_conjunctive false false)
    verdict_conjunctive_fold_ok &&
  fold_conservation_verdict_beq
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_disjunctive false false)
    verdict_disjunctive_fold_ok &&
  fold_conservation_verdict_beq
    (evaluate_fold_conservation_close
       fold_conservation_unwired fold_conjunctive true false)
    verdict_green_invent_refuse &&
  fold_conservation_verdict_beq
    (evaluate_fold_conservation_close
       fold_conservation_proved fold_conjunctive false true)
    verdict_production_wired_refuse.

Lemma fold_conservation_coherence_scaffold_true :
  fold_conservation_coherence_scaffold = true.
Proof.
  unfold fold_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem fold_conservation_coherence_scaffold_theorem :
  evaluate_fold_conservation_close
    fold_conservation_proved fold_conjunctive false false =
    verdict_conjunctive_fold_ok /\
  evaluate_fold_conservation_close
    fold_conservation_proved fold_disjunctive false false =
    verdict_disjunctive_fold_ok /\
  evaluate_fold_conservation_close
    fold_conservation_unwired fold_conjunctive true false =
    verdict_green_invent_refuse /\
  evaluate_fold_conservation_close
    fold_conservation_proved fold_conjunctive false true =
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
  | claim_fold_conservation.

Definition fold_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition fold_conservation_knowing_fiber_ok : bool :=
  fold_conservation_fiber_ok fiber_quantum_knowing.

Definition fold_conservation_meso_acting_ok : bool :=
  fold_conservation_fiber_ok fiber_meso_acting.

Lemma fold_conservation_knowing_fiber_ok_true :
  fold_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma fold_conservation_meso_acting_not_ok :
  fold_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem fold_conservation_routes_knowing_not_meso :
  fold_conservation_knowing_fiber_ok = true /\
  fold_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply fold_conservation_knowing_fiber_ok_true.
  - apply fold_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  fold_conservation_knowing_fiber_ok &&
  negb fold_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, fold_conservation_knowing_fiber_ok,
    fold_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — fold identity + fiber + FP-01 pins             *)
(* ------------------------------------------------------------------ *)

Theorem fold_conservation_fixture_scaffold :
  fold_classifiers [] fold_conjunctive patternFeatureZero = true /\
  fold_classifiers [] fold_disjunctive patternFeatureZero = false /\
  fold_classifiers bond_forming_structure_enabling_kinds fold_conjunctive
    patternFeatureBondForming = false /\
  fold_classifiers bond_forming_structure_enabling_kinds fold_disjunctive
    patternFeatureBondForming = true /\
  evaluate_fold_conservation_close
    fold_conservation_unwired fold_conjunctive false false =
    verdict_unwired_ok /\
  fold_conservation_knowing_fiber_ok = true /\
  fold_conservation_meso_acting_ok = false /\
  fp01FoldProved = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — fold conservation)   *)
(* ------------------------------------------------------------------ *)

Definition patternClassifierFoldsAuthority : string :=
  "umst/umst-chem/src/pattern_classifier_folds.rs".

Definition chemIntProveFp01FoldsAuthority : string :=
  "CHEM-INT-PROVE-FP-01-FOLDS".

Definition patternClassifierFoldsMarker : string :=
  "chem_l0_pattern_classifier_folds_v1".

Definition foldConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-FOLD-CONSERVATION".

Definition foldConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-FOLD-CONSERVATION FP-01 classifier fold conservation conjunctive disjunctive fold identity conserved predicates folds design scaffold fp01FoldProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second fold axiom not GREEN DFT not physics GREEN not production_wired".

Lemma fold_conservation_cell_id :
  foldConservationCellId = "CHEM-FORMAL-Q-COQ-FOLD-CONSERVATION".
Proof. reflexivity. Qed.

Lemma fold_conservation_cites_pattern_classifier_folds_rs :
  patternClassifierFoldsAuthority <> "".
Proof. discriminate. Qed.

Lemma fold_conservation_cites_int_prove_fp_01_folds :
  chemIntProveFp01FoldsAuthority = "CHEM-INT-PROVE-FP-01-FOLDS".
Proof. reflexivity. Qed.

Lemma fold_conservation_cites_marker :
  patternClassifierFoldsMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second fold axiom *)
(* ------------------------------------------------------------------ *)

Definition foldSecondLawConservationFraming : string :=
  "second_law_conservation_fold_one_axiom_not_second_fold_axiom".

Lemma fold_not_second_fold_axiom :
  foldSecondLawConservationFraming <> "second_fold_axiom".
Proof. discriminate. Qed.

Lemma fold_second_law_conservation_framing :
  foldSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma fold_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma fold_conservation_modality_unwired :
  foldConservationModalityCurrent = fold_conservation_unwired.
Proof. reflexivity. Qed.

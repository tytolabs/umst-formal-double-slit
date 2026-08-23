(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PullbackConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: CAT-02 pullback/pushout conservation. Shared    *)
(*  substructure identity conserved under limit/colimit scaffolds;       *)
(*  universal properties Unwired not Proved; not CAT-02 Proved.          *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — pullback conservation is not a second       *)
(*  axiom. Not a 118² GREEN table.                                     *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  CAT-02 pullback conservation modality (TYPE-03 — Unwired)           *)
(* ------------------------------------------------------------------ *)

Inductive PullbackConservationModality : Type :=
  | pullback_conservation_unwired
  | pullback_conservation_assumed
  | pullback_conservation_proved
  | pullback_conservation_surrogate.

Definition pullbackConservationModalityCurrent : PullbackConservationModality :=
  pullback_conservation_unwired.

(* ------------------------------------------------------------------ *)
(*  SharedSubstructure / Pullback / Pushout inductive scaffold          *)
(* ------------------------------------------------------------------ *)

Inductive SubstructureOverlapTag : Type :=
  | overlap_quartz_vein
  | overlap_sulfide_matrix
  | overlap_carbonate_gangue.

Inductive SharedSubstructureDiagramKind : Type :=
  | diagram_pullback
  | diagram_pushout.

Record SharedSubstructureDiagramScaffold : Type := {
  diagram_kind : SharedSubstructureDiagramKind;
  diagram_overlap : SubstructureOverlapTag;
  diagram_left_leg : nat;
  diagram_right_leg : nat
}.

Definition overlap_tag_beq (a b : SubstructureOverlapTag) : bool :=
  match a, b with
  | overlap_quartz_vein, overlap_quartz_vein => true
  | overlap_sulfide_matrix, overlap_sulfide_matrix => true
  | overlap_carbonate_gangue, overlap_carbonate_gangue => true
  | _, _ => false
  end.

Lemma overlap_tag_beq_refl (t : SubstructureOverlapTag) :
  overlap_tag_beq t t = true.
Proof. destruct t; reflexivity. Qed.

Definition diagram_kind_beq (a b : SharedSubstructureDiagramKind) : bool :=
  match a, b with
  | diagram_pullback, diagram_pullback => true
  | diagram_pushout, diagram_pushout => true
  | _, _ => false
  end.

Lemma diagram_kind_beq_refl (k : SharedSubstructureDiagramKind) :
  diagram_kind_beq k k = true.
Proof. destruct k; reflexivity. Qed.

Definition legs_distinct (d : SharedSubstructureDiagramScaffold) : bool :=
  negb (Nat.eqb d.(diagram_left_leg) d.(diagram_right_leg)).

Definition pullback_quartz_scaffold : SharedSubstructureDiagramScaffold :=
  {| diagram_kind := diagram_pullback;
     diagram_overlap := overlap_quartz_vein;
     diagram_left_leg := 0;
     diagram_right_leg := 1 |}.

Definition pushout_sulfide_scaffold : SharedSubstructureDiagramScaffold :=
  {| diagram_kind := diagram_pushout;
     diagram_overlap := overlap_sulfide_matrix;
     diagram_left_leg := 0;
     diagram_right_leg := 1 |}.

Definition shared_substructure_witness (d : SharedSubstructureDiagramScaffold) :
  SubstructureOverlapTag :=
  d.(diagram_overlap).

(* ------------------------------------------------------------------ *)
(*  Universal-property / CAT-02 pins (structure witnesses — not Proved) *)
(* ------------------------------------------------------------------ *)

Definition universalPropertiesProved : bool := false.

Lemma universal_properties_proved_false : universalPropertiesProved = false.
Proof. reflexivity. Qed.

Definition cat02PullbackProved : bool := false.

Lemma cat02_pullback_not_proved : cat02PullbackProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Pullback overlap identity conservation                              *)
(* ------------------------------------------------------------------ *)

Definition pullback_overlap_conserved (d : SharedSubstructureDiagramScaffold) : bool :=
  match d.(diagram_kind) with
  | diagram_pullback =>
      overlap_tag_beq
        (shared_substructure_witness d)
        d.(diagram_overlap)
  | diagram_pushout => false
  end.

Lemma pullback_quartz_overlap_conserved :
  pullback_overlap_conserved pullback_quartz_scaffold = true.
Proof.
  unfold pullback_overlap_conserved, pullback_quartz_scaffold.
  simpl. reflexivity.
Qed.

Theorem pullback_identity_conservation :
  forall d : SharedSubstructureDiagramScaffold,
    d.(diagram_kind) = diagram_pullback ->
    legs_distinct d = true ->
    pullback_overlap_conserved d = true.
Proof.
  intros d Hkind Hlegs.
  unfold pullback_overlap_conserved, shared_substructure_witness.
  rewrite Hkind.
  rewrite (overlap_tag_beq_refl (diagram_overlap d)).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pushout overlap identity conservation                               *)
(* ------------------------------------------------------------------ *)

Definition pushout_overlap_conserved (d : SharedSubstructureDiagramScaffold) : bool :=
  match d.(diagram_kind) with
  | diagram_pushout =>
      overlap_tag_beq
        (shared_substructure_witness d)
        d.(diagram_overlap)
  | diagram_pullback => false
  end.

Lemma pushout_sulfide_overlap_conserved :
  pushout_overlap_conserved pushout_sulfide_scaffold = true.
Proof.
  unfold pushout_overlap_conserved, pushout_sulfide_scaffold.
  simpl. reflexivity.
Qed.

Theorem pushout_identity_conservation :
  forall d : SharedSubstructureDiagramScaffold,
    d.(diagram_kind) = diagram_pushout ->
    legs_distinct d = true ->
    pushout_overlap_conserved d = true.
Proof.
  intros d Hkind Hlegs.
  unfold pushout_overlap_conserved, shared_substructure_witness.
  rewrite Hkind.
  rewrite (overlap_tag_beq_refl (diagram_overlap d)).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  limitNotXor — pullback limit vs pushout colimit, not XOR enum       *)
(* ------------------------------------------------------------------ *)

Definition is_limit_kind (k : SharedSubstructureDiagramKind) : bool :=
  match k with
  | diagram_pullback => true
  | diagram_pushout => false
  end.

Lemma pullback_is_limit :
  is_limit_kind diagram_pullback = true.
Proof. reflexivity. Qed.

Lemma pushout_not_limit :
  is_limit_kind diagram_pushout = false.
Proof. reflexivity. Qed.

Definition limitNotXor : bool :=
  is_limit_kind pullback_quartz_scaffold.(diagram_kind) &&
  negb (is_limit_kind pushout_sulfide_scaffold.(diagram_kind)).

Lemma limit_not_xor_true : limitNotXor = true.
Proof.
  unfold limitNotXor, pullback_quartz_scaffold, pushout_sulfide_scaffold.
  simpl. reflexivity.
Qed.

Theorem limit_not_colimit_xor :
  limitNotXor = true /\
  is_limit_kind diagram_pullback = true /\
  is_limit_kind diagram_pushout = false.
Proof.
  split.
  - apply limit_not_xor_true.
  - split; [apply pullback_is_limit | apply pushout_not_limit].
Qed.

(* ------------------------------------------------------------------ *)
(*  Degenerate legs refuse — identity conservation requires distinct legs *)
(* ------------------------------------------------------------------ *)

Definition degenerate_carbonate_scaffold : SharedSubstructureDiagramScaffold :=
  {| diagram_kind := diagram_pullback;
     diagram_overlap := overlap_carbonate_gangue;
     diagram_left_leg := 2;
     diagram_right_leg := 2 |}.

Lemma degenerate_legs_not_distinct :
  legs_distinct degenerate_carbonate_scaffold = false.
Proof.
  unfold legs_distinct, degenerate_carbonate_scaffold.
  simpl. reflexivity.
Qed.

Lemma valid_pullback_legs_distinct :
  legs_distinct pullback_quartz_scaffold = true.
Proof.
  unfold legs_distinct, pullback_quartz_scaffold.
  simpl. reflexivity.
Qed.

Lemma valid_pushout_legs_distinct :
  legs_distinct pushout_sulfide_scaffold = true.
Proof.
  unfold legs_distinct, pushout_sulfide_scaffold.
  simpl. reflexivity.
Qed.

Theorem shared_substructure_fixture_scaffold :
  pullback_overlap_conserved pullback_quartz_scaffold = true /\
  pushout_overlap_conserved pushout_sulfide_scaffold = true /\
  legs_distinct pullback_quartz_scaffold = true /\
  legs_distinct pushout_sulfide_scaffold = true.
Proof.
  split.
  - apply pullback_quartz_overlap_conserved.
  - split.
    + apply pushout_sulfide_overlap_conserved.
    + split; [apply valid_pullback_legs_distinct | apply valid_pushout_legs_distinct].
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pullback conservation) *)
(* ------------------------------------------------------------------ *)

Definition sharedSubstructureLimitsAuthority : string :=
  "umst/umst-chem/src/shared_substructure_limits.rs".

Definition sharedSubstructureLeanAuthority : string :=
  "umst/umst-formal/Lean/Chem/SharedSubstructure.lean".

Definition chemL0Cat02Authority : string :=
  "CHEM-L0-CAT-02".

Definition chemIntProveCat02PullbackAuthority : string :=
  "CHEM-INT-PROVE-CAT-02-PULLBACK".

Definition pullbackConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PULLBACK-CONSERVATION".

Definition pullbackConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PULLBACK-CONSERVATION CAT-02 pullback pushout conservation SharedSubstructure overlap identity conservation pullback pushout scaffold limitNotXor not XOR universalPropertiesProved false cat02PullbackProved false not 118 squared GREEN table Unwired one axiom second law conservation not second pullback axiom not GREEN DFT not physics GREEN not production_wired".

Lemma pullback_conservation_cell_id :
  pullbackConservationCellId =
  "CHEM-FORMAL-Q-COQ-PULLBACK-CONSERVATION".
Proof. reflexivity. Qed.

Lemma pullback_cites_shared_substructure_rs :
  sharedSubstructureLimitsAuthority <>
  "".
Proof. discriminate. Qed.

Lemma pullback_cites_lean :
  sharedSubstructureLeanAuthority <>
  "".
Proof. discriminate. Qed.

Lemma pullback_cites_l0_cat_02 :
  chemL0Cat02Authority = "CHEM-L0-CAT-02".
Proof. reflexivity. Qed.

Lemma pullback_cites_int_prove_cat_02 :
  chemIntProveCat02PullbackAuthority <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second pullback   *)
(* ------------------------------------------------------------------ *)

Definition pullbackSecondLawConservationFraming : string :=
  "second_law_conservation_pullback_one_axiom_not_second_pullback_axiom".

Lemma pullback_not_second_pullback_axiom :
  pullbackSecondLawConservationFraming <>
  "second_pullback_axiom".
Proof. discriminate. Qed.

Lemma pullback_second_law_conservation_framing :
  pullbackSecondLawConservationFraming <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma pullback_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma pullback_modality_unwired :
  pullbackConservationModalityCurrent = pullback_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EffectConservation.v                                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: TYPE-04 dissipative effect conservation.        *)
(*  Forward Refine requires positive ChemStamp/Landauer witness; free  *)
(*  purification refuse; reverse contaminate typed. Modality Unwired.  *)
(*  type04EffectProved Unwired not Proved. Not 118² GREEN table.       *)
(*  Geometry routes knowing/quantum fiber not meso acting.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — effect conservation is not a second axiom.  *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  TYPE-04 effect conservation modality (Unwired / Assumed /         *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive EffectConservationModality : Type :=
  | effect_conservation_unwired
  | effect_conservation_assumed
  | effect_conservation_proved
  | effect_conservation_surrogate.

Definition effectConservationModalityCurrent : EffectConservationModality :=
  effect_conservation_unwired.

Definition effect_lattice_cardinality : nat := 4.

Lemma effect_lattice_cardinality_is_four :
  effect_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma effect_lattice_not_118_squared :
  negb (Nat.eqb effect_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold effect_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Refine direction — forward refine vs reverse contaminate            *)
(* ------------------------------------------------------------------ *)

Inductive refine_direction : Type :=
  | forward_refine
  | reverse_contaminate.

Definition refine_direction_forward_requires_dissipation (d : refine_direction) : bool :=
  match d with
  | forward_refine => true
  | reverse_contaminate => false
  end.

Lemma forward_refine_requires_dissipation :
  refine_direction_forward_requires_dissipation forward_refine = true.
Proof. reflexivity. Qed.

Lemma reverse_contaminate_no_forward_dissipation :
  refine_direction_forward_requires_dissipation reverse_contaminate = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ChemStamp / Landauer dissipation witness                            *)
(* ------------------------------------------------------------------ *)

Record chem_stamp_witness : Type := {
  dissipation_microjoules : nat
}.

Definition chemStampWitnessZero : chem_stamp_witness :=
  {| dissipation_microjoules := 0 |}.

Definition chemStampWitnessPositiveScaffold : chem_stamp_witness :=
  {| dissipation_microjoules := 1 |}.

Definition chem_stamp_witness_positive (w : chem_stamp_witness) : bool :=
  Nat.ltb 0 (dissipation_microjoules w).

Lemma chem_stamp_zero_not_positive :
  chem_stamp_witness_positive chemStampWitnessZero = false.
Proof. reflexivity. Qed.

Lemma chem_stamp_positive_scaffold_is_positive :
  chem_stamp_witness_positive chemStampWitnessPositiveScaffold = true.
Proof. reflexivity. Qed.

Lemma chem_stamp_positive_scaffold_gt_zero :
  0 < dissipation_microjoules chemStampWitnessPositiveScaffold.
Proof. simpl. apply Nat.lt_0_succ. Qed.

(* ------------------------------------------------------------------ *)
(*  Refine effect kind — pure vs dissipative typing scaffold            *)
(* ------------------------------------------------------------------ *)

Inductive refine_effect_kind : Type :=
  | effect_kind_pure
  | effect_kind_dissipative (w : chem_stamp_witness).

Definition refine_effect_kind_dissipative_positive (k : refine_effect_kind) : bool :=
  match k with
  | effect_kind_pure => false
  | effect_kind_dissipative w => chem_stamp_witness_positive w
  end.

Definition refine_effect_kind_of
  (d : refine_direction) (w : chem_stamp_witness) : refine_effect_kind :=
  match d with
  | forward_refine =>
      if chem_stamp_witness_positive w
      then effect_kind_dissipative w
      else effect_kind_pure
  | reverse_contaminate => effect_kind_dissipative w
  end.

Lemma forward_positive_witness_effect_kind_dissipative :
  refine_effect_kind_of forward_refine chemStampWitnessPositiveScaffold =
  effect_kind_dissipative chemStampWitnessPositiveScaffold.
Proof. reflexivity. Qed.

Lemma forward_zero_witness_effect_kind_pure :
  refine_effect_kind_of forward_refine chemStampWitnessZero = effect_kind_pure.
Proof. reflexivity. Qed.

Lemma reverse_contaminate_effect_kind_dissipative :
  refine_effect_kind_of reverse_contaminate chemStampWitnessZero =
  effect_kind_dissipative chemStampWitnessZero.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Effect conservation close verdict — fail-closed lattice             *)
(* ------------------------------------------------------------------ *)

Inductive effect_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_forward_dissipative_ok
  | verdict_free_purification_refuse
  | verdict_reverse_contaminate_ok
  | verdict_green_invent_refuse.

Definition effect_conservation_verdict_ok (v : effect_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_forward_dissipative_ok => true
  | verdict_reverse_contaminate_ok => true
  | _ => false
  end.

Definition effect_conservation_verdict_beq
  (v1 v2 : effect_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_forward_dissipative_ok, verdict_forward_dissipative_ok => true
  | verdict_free_purification_refuse, verdict_free_purification_refuse => true
  | verdict_reverse_contaminate_ok, verdict_reverse_contaminate_ok => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | _, _ => false
  end.

Definition evaluate_effect_conservation_close
  (m : EffectConservationModality) (d : refine_direction) (w : chem_stamp_witness)
  (claim_physics_green : bool) : effect_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else
    match m with
    | effect_conservation_unwired => verdict_unwired_ok
    | effect_conservation_assumed
    | effect_conservation_proved
    | effect_conservation_surrogate =>
        match d with
        | forward_refine =>
            if chem_stamp_witness_positive w
            then verdict_forward_dissipative_ok
            else verdict_free_purification_refuse
        | reverse_contaminate => verdict_reverse_contaminate_ok
        end
    end.

Definition forward_refine_authorized
  (w : chem_stamp_witness) (claim_physics_green : bool) : bool :=
  match evaluate_effect_conservation_close
          effect_conservation_proved forward_refine w claim_physics_green with
  | verdict_forward_dissipative_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Dissipative effect law cells — four laws, open @ Unwired            *)
(* ------------------------------------------------------------------ *)

Inductive dissipative_effect_law : Type :=
  | law_forward_requires_witness
  | law_zero_witness_refuse
  | law_reverse_contaminate_typed
  | law_green_invent_refuse.

Definition dissipative_effect_law_count : nat := 4.

Lemma dissipative_effect_law_count_is_four :
  dissipative_effect_law_count = 4.
Proof. reflexivity. Qed.

Inductive dissipative_effect_law_witness : Type :=
  | law_witness_open
  | law_witness_proved.

Definition evaluate_dissipative_effect_law_witness
  (law : dissipative_effect_law) (m : EffectConservationModality)
  : dissipative_effect_law_witness :=
  match m with
  | effect_conservation_unwired
  | effect_conservation_assumed
  | effect_conservation_surrogate => law_witness_open
  | effect_conservation_proved => law_witness_proved
  end.

Lemma all_dissipative_effect_laws_open_at_unwired :
  evaluate_dissipative_effect_law_witness law_forward_requires_witness
    effect_conservation_unwired = law_witness_open /\
  evaluate_dissipative_effect_law_witness law_zero_witness_refuse
    effect_conservation_unwired = law_witness_open /\
  evaluate_dissipative_effect_law_witness law_reverse_contaminate_typed
    effect_conservation_unwired = law_witness_open /\
  evaluate_dissipative_effect_law_witness law_green_invent_refuse
    effect_conservation_unwired = law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  TYPE-04 pins (structure witnesses — effect laws not Proved)         *)
(* ------------------------------------------------------------------ *)

Definition type04EffectProved : bool := false.

Lemma type04_effect_proved_false : type04EffectProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without positive witness (lemma)                      *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_positive_witness :
  evaluate_effect_conservation_close
    effect_conservation_unwired forward_refine chemStampWitnessZero false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_green :
  evaluate_effect_conservation_close
    effect_conservation_unwired forward_refine chemStampWitnessZero false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_positive_witness. Qed.

Lemma unwired_verdict_ok_without_positive_witness :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_unwired forward_refine chemStampWitnessZero false) =
  true.
Proof.
  unfold effect_conservation_verdict_ok.
  rewrite unwired_close_without_positive_witness.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Forward Refine requires positive ChemStamp/Landauer witness         *)
(* ------------------------------------------------------------------ *)

Lemma forward_refine_positive_witness_ok :
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false =
  verdict_forward_dissipative_ok.
Proof. reflexivity. Qed.

Theorem forward_refine_requires_positive_chem_stamp_landauer_witness :
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false =
  verdict_forward_dissipative_ok /\
  forward_refine_authorized chemStampWitnessPositiveScaffold false = true.
Proof.
  split.
  - apply forward_refine_positive_witness_ok.
  - unfold forward_refine_authorized.
    rewrite forward_refine_positive_witness_ok.
    reflexivity.
Qed.

Lemma forward_refine_positive_verdict_ok :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false) =
  true.
Proof.
  unfold effect_conservation_verdict_ok.
  rewrite forward_refine_positive_witness_ok.
  reflexivity.
Qed.

Lemma forward_refine_positive_still_not_physics_green :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false) =
  true /\
  type04EffectProved = false.
Proof.
  split.
  - apply forward_refine_positive_verdict_ok.
  - apply type04_effect_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — forward with non-positive witness        *)
(* ------------------------------------------------------------------ *)

Lemma free_purification_refuse :
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessZero false =
  verdict_free_purification_refuse.
Proof. reflexivity. Qed.

Theorem forward_refine_zero_witness_refused :
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessZero false =
  verdict_free_purification_refuse /\
  forward_refine_authorized chemStampWitnessZero false = false.
Proof.
  split.
  - apply free_purification_refuse.
  - unfold forward_refine_authorized.
    rewrite free_purification_refuse.
    reflexivity.
Qed.

Theorem free_purification_not_ok :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_proved forward_refine chemStampWitnessZero false) =
  false.
Proof.
  unfold effect_conservation_verdict_ok.
  rewrite free_purification_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Reverse contaminate typed — allowed without forward cost            *)
(* ------------------------------------------------------------------ *)

Lemma reverse_contaminate_typed :
  evaluate_effect_conservation_close
    effect_conservation_proved reverse_contaminate chemStampWitnessZero false =
  verdict_reverse_contaminate_ok.
Proof. reflexivity. Qed.

Theorem reverse_contaminate_scaffold_ok_without_forward_cost :
  evaluate_effect_conservation_close
    effect_conservation_proved reverse_contaminate chemStampWitnessZero false =
  verdict_reverse_contaminate_ok.
Proof. apply reverse_contaminate_typed. Qed.

Lemma reverse_contaminate_verdict_ok :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_proved reverse_contaminate chemStampWitnessZero false) =
  true.
Proof.
  unfold effect_conservation_verdict_ok.
  rewrite reverse_contaminate_typed.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_effect_conservation_close
    effect_conservation_unwired forward_refine chemStampWitnessPositiveScaffold true =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  effect_conservation_verdict_ok
    (evaluate_effect_conservation_close
       effect_conservation_unwired forward_refine chemStampWitnessPositiveScaffold true) =
  false.
Proof.
  unfold effect_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Dissipative effect coherence scaffold — fixture witnesses           *)
(* ------------------------------------------------------------------ *)

Definition dissipative_effect_coherence_scaffold : bool :=
  effect_conservation_verdict_beq
    (evaluate_effect_conservation_close
       effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false)
    verdict_forward_dissipative_ok &&
  effect_conservation_verdict_beq
    (evaluate_effect_conservation_close
       effect_conservation_proved forward_refine chemStampWitnessZero false)
    verdict_free_purification_refuse &&
  effect_conservation_verdict_beq
    (evaluate_effect_conservation_close
       effect_conservation_proved reverse_contaminate chemStampWitnessZero false)
    verdict_reverse_contaminate_ok &&
  effect_conservation_verdict_beq
    (evaluate_effect_conservation_close
       effect_conservation_unwired forward_refine chemStampWitnessPositiveScaffold true)
    verdict_green_invent_refuse.

Lemma dissipative_effect_coherence_scaffold_true :
  dissipative_effect_coherence_scaffold = true.
Proof.
  unfold dissipative_effect_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem effect_conservation_coherence_scaffold :
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false =
    verdict_forward_dissipative_ok /\
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessZero false =
    verdict_free_purification_refuse /\
  evaluate_effect_conservation_close
    effect_conservation_proved reverse_contaminate chemStampWitnessZero false =
    verdict_reverse_contaminate_ok /\
  evaluate_effect_conservation_close
    effect_conservation_unwired forward_refine chemStampWitnessPositiveScaffold true =
    verdict_green_invent_refuse.
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
  | claim_effect_conservation.

Definition effect_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition effect_conservation_knowing_fiber_ok : bool :=
  effect_conservation_fiber_ok fiber_quantum_knowing.

Definition effect_conservation_meso_acting_ok : bool :=
  effect_conservation_fiber_ok fiber_meso_acting.

Lemma effect_conservation_knowing_fiber_ok_true :
  effect_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma effect_conservation_meso_acting_not_ok :
  effect_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem effect_conservation_routes_knowing_not_meso :
  effect_conservation_knowing_fiber_ok = true /\
  effect_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply effect_conservation_knowing_fiber_ok_true.
  - apply effect_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  effect_conservation_knowing_fiber_ok &&
  negb effect_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, effect_conservation_knowing_fiber_ok,
    effect_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — effect + witness + fiber + TYPE-04 pins          *)
(* ------------------------------------------------------------------ *)

Theorem effect_conservation_fixture_scaffold :
  evaluate_effect_conservation_close
    effect_conservation_unwired forward_refine chemStampWitnessZero false =
    verdict_unwired_ok /\
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessPositiveScaffold false =
    verdict_forward_dissipative_ok /\
  evaluate_effect_conservation_close
    effect_conservation_proved forward_refine chemStampWitnessZero false =
    verdict_free_purification_refuse /\
  evaluate_effect_conservation_close
    effect_conservation_proved reverse_contaminate chemStampWitnessZero false =
    verdict_reverse_contaminate_ok /\
  effect_conservation_knowing_fiber_ok = true /\
  effect_conservation_meso_acting_ok = false /\
  type04EffectProved = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — effect conservation) *)
(* ------------------------------------------------------------------ *)

Definition effectConservationAuthority : string :=
  "umst/umst-chem/src/refine_effect_types.rs".

Definition chemL0Type04Authority : string :=
  "CHEM-L0-TYPE-04".

Definition chemIntProveType04EffectAuthority : string :=
  "CHEM-INT-PROVE-TYPE-04-EFFECT".

Definition contaminationReverseRefineAuthority : string :=
  "umst/umst-chem/src/contamination_reverse_refine.rs".

Definition processingRefiningAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition effectConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-EFFECT-CONSERVATION".

Definition effectConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-EFFECT-CONSERVATION TYPE-04 dissipative effect conservation forward Refine requires positive ChemStamp Landauer witness free purification refuse reverse contaminate typed geometry knowing quantum fiber not meso acting type04EffectProved false Unwired one axiom second law conservation not second effect axiom not GREEN DFT not physics GREEN not production_wired".

Lemma effect_conservation_cell_id :
  effectConservationCellId = "CHEM-FORMAL-Q-COQ-EFFECT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma effect_conservation_cites_refine_effect_types_rs :
  effectConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma effect_conservation_cites_l0_type_04 :
  chemL0Type04Authority = "CHEM-L0-TYPE-04".
Proof. reflexivity. Qed.

Lemma effect_conservation_cites_int_prove_type_04_effect :
  chemIntProveType04EffectAuthority <> "".
Proof. discriminate. Qed.

Lemma effect_conservation_cites_contamination_reverse_refine :
  contaminationReverseRefineAuthority <> "".
Proof. discriminate. Qed.

Lemma effect_conservation_cites_processing_refining :
  processingRefiningAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second effect     *)
(* ------------------------------------------------------------------ *)

Definition effectSecondLawConservationFraming : string :=
  "second_law_conservation_effect_one_axiom_not_second_effect_axiom".

Lemma effect_not_second_effect_axiom :
  effectSecondLawConservationFraming <> "second_effect_axiom".
Proof. discriminate. Qed.

Lemma effect_second_law_conservation_framing :
  effectSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma effect_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma effect_conservation_modality_unwired :
  effectConservationModalityCurrent = effect_conservation_unwired.
Proof. reflexivity. Qed.

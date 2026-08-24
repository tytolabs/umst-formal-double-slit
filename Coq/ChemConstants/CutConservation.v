(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CutConservation.v                                     *)
(*                                                                      *)
(*  Knowing-fiber Coq: GRAPH-02 cut conservation. Named ore/waste     *)
(*  partition complement conserved; recycle loop named; Fe Z=26 Cu Z=29 *)
(*  Og Z=118; trivial cut fail-closed; GREEN invent fail-closed;      *)
(*  Proved-without-bar fail-closed. Modality Unwired; graph02CutProved  *)
(*  Unwired not Proved. Cut separation morphisms not bond/reaction     *)
(*  edges. Geometry routes knowing/quantum fiber not meso acting.       *)
(*  Not 118² GREEN table.                                              *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — cut conservation is not a second axiom.      *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  GRAPH-02 cut conservation modality (Unwired / Assumed /            *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive CutConservationModality : Type :=
  | cut_conservation_unwired
  | cut_conservation_assumed
  | cut_conservation_proved
  | cut_conservation_surrogate.

Definition cutConservationModalityCurrent : CutConservationModality :=
  cut_conservation_unwired.

Definition cut_lattice_cardinality : nat := 4.

Lemma cut_lattice_cardinality_is_four :
  cut_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma cut_lattice_not_118_squared :
  negb (Nat.eqb cut_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold cut_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — cut element conservation scaffold (not 118² table)   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition cut_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition cut_element_iron_z : nat := 26.
Definition cut_element_copper_z : nat := 29.
Definition cut_element_oganesson_z : nat := 118.

Lemma cut_iron_z_is_26 :
  cut_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma cut_copper_z_is_29 :
  cut_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma cut_oganesson_z_is_118 :
  cut_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma cut_fe_cu_z_valid :
  cut_element_z_valid cut_element_iron_z = true /\
  cut_element_z_valid cut_element_copper_z = true.
Proof.
  split; unfold cut_element_z_valid, cut_element_iron_z,
    cut_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma cut_oganesson_z_valid :
  cut_element_z_valid cut_element_oganesson_z = true.
Proof.
  unfold cut_element_z_valid, cut_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cut side partition — source/sink complement conserved               *)
(* ------------------------------------------------------------------ *)

Inductive cut_side : Type :=
  | cut_side_source
  | cut_side_sink.

Definition cut_side_beq (s1 s2 : cut_side) : bool :=
  match s1, s2 with
  | cut_side_source, cut_side_source => true
  | cut_side_sink, cut_side_sink => true
  | _, _ => false
  end.

Definition cut_side_complement (s : cut_side) : cut_side :=
  match s with
  | cut_side_source => cut_side_sink
  | cut_side_sink => cut_side_source
  end.

Lemma cut_side_complement_source :
  cut_side_complement cut_side_source = cut_side_sink.
Proof. reflexivity. Qed.

Lemma cut_side_complement_sink :
  cut_side_complement cut_side_sink = cut_side_source.
Proof. reflexivity. Qed.

Lemma cut_side_complement_involutive (s : cut_side) :
  cut_side_complement (cut_side_complement s) = s.
Proof.
  destruct s; reflexivity.
Qed.

Theorem cut_partition_complement_conserved :
  cut_side_complement cut_side_source = cut_side_sink /\
  cut_side_complement cut_side_sink = cut_side_source.
Proof.
  split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named cut roles — ore/waste/recycle; cut ≠ bond                     *)
(* ------------------------------------------------------------------ *)

Inductive refining_cut_role : Type :=
  | cut_role_ore_fraction
  | cut_role_waste_tail
  | cut_role_recycle_loop.

Definition refining_cut_role_beq (r1 r2 : refining_cut_role) : bool :=
  match r1, r2 with
  | cut_role_ore_fraction, cut_role_ore_fraction => true
  | cut_role_waste_tail, cut_role_waste_tail => true
  | cut_role_recycle_loop, cut_role_recycle_loop => true
  | _, _ => false
  end.

Definition refining_cut_role_default_side (r : refining_cut_role) : cut_side :=
  match r with
  | cut_role_ore_fraction => cut_side_source
  | cut_role_waste_tail => cut_side_sink
  | cut_role_recycle_loop => cut_side_source
  end.

Lemma ore_waste_default_sides_distinct :
  refining_cut_role_default_side cut_role_ore_fraction <>
  refining_cut_role_default_side cut_role_waste_tail.
Proof. discriminate. Qed.

Lemma ore_waste_separation_typed :
  refining_cut_role_default_side cut_role_ore_fraction = cut_side_source /\
  refining_cut_role_default_side cut_role_waste_tail = cut_side_sink.
Proof. split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Refining graph cut / separation records — named identity conserved  *)
(* ------------------------------------------------------------------ *)

Record refining_graph_cut : Type := {
  cut_id : nat;
  cut_role_tag : refining_cut_role;
  cut_source_side : cut_side;
  cut_element_z : nat
}.

Record cut_separation : Type := {
  cut_sep_cut : refining_graph_cut;
  cut_sep_level : nat
}.

Definition cutSeparationNontrivial (s : cut_separation) : bool :=
  Nat.ltb 0 (cut_sep_level s).

Definition cutSinkSide (c : refining_graph_cut) : cut_side :=
  cut_side_complement (cut_source_side c).

Definition cutIsSource (c : refining_graph_cut) (side : cut_side) : bool :=
  cut_side_beq (cut_source_side c) side.

Definition cutIdentityConserved (c1 c2 : refining_graph_cut) : bool :=
  Nat.eqb c1.(cut_id) c2.(cut_id) &&
  refining_cut_role_beq c1.(cut_role_tag) c2.(cut_role_tag) &&
  cut_side_beq c1.(cut_source_side) c2.(cut_source_side) &&
  Nat.eqb c1.(cut_element_z) c2.(cut_element_z).

Definition cutOreWasteFe : refining_graph_cut :=
  {| cut_id := 1;
     cut_role_tag := cut_role_ore_fraction;
     cut_source_side := cut_side_source;
     cut_element_z := cut_element_iron_z |}.

Definition cutRecycleCu : refining_graph_cut :=
  {| cut_id := 2;
     cut_role_tag := cut_role_recycle_loop;
     cut_source_side := cut_side_source;
     cut_element_z := cut_element_copper_z |}.

Definition cutOganessonPin : refining_graph_cut :=
  {| cut_id := 3;
     cut_role_tag := cut_role_ore_fraction;
     cut_source_side := cut_side_source;
     cut_element_z := cut_element_oganesson_z |}.

Definition cutSeparationOreWasteL1 : cut_separation :=
  {| cut_sep_cut := cutOreWasteFe; cut_sep_level := 1 |}.

Definition cutSeparationRecycleL1 : cut_separation :=
  {| cut_sep_cut := cutRecycleCu; cut_sep_level := 1 |}.

Definition cutSeparationOreWasteTrivial : cut_separation :=
  {| cut_sep_cut := cutOreWasteFe; cut_sep_level := 0 |}.

Lemma cut_ore_waste_fe_nontrivial :
  cutSeparationNontrivial cutSeparationOreWasteL1 = true.
Proof. reflexivity. Qed.

Lemma cut_ore_waste_fe_z_pin :
  cutOreWasteFe.(cut_element_z) = 26.
Proof.
  unfold cutOreWasteFe, cut_element_iron_z.
  reflexivity.
Qed.

Lemma cut_ore_waste_fe_identity_conserved :
  cutIdentityConserved cutOreWasteFe cutOreWasteFe = true.
Proof. reflexivity. Qed.

Lemma cut_ore_waste_fe_source_sink :
  cutIsSource cutOreWasteFe cut_side_source = true /\
  cutIsSource cutOreWasteFe cut_side_sink = false /\
  cutSinkSide cutOreWasteFe = cut_side_sink.
Proof.
  repeat split; reflexivity.
Qed.

Lemma cut_recycle_loop_named :
  refining_cut_role_beq cutRecycleCu.(cut_role_tag) cut_role_recycle_loop = true /\
  cut_element_z_valid cutRecycleCu.(cut_element_z) = true.
Proof.
  split; unfold cutRecycleCu; reflexivity.
Qed.

Lemma cut_ore_waste_trivial_not_nontrivial :
  cutSeparationNontrivial cutSeparationOreWasteTrivial = false.
Proof. reflexivity. Qed.

Definition recycle_loop_named_vertex : bool :=
  Nat.ltb 0 cutRecycleCu.(cut_id).

Lemma recycle_loop_named_vertex_true :
  recycle_loop_named_vertex = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cut ≠ bond — separation morphisms not bond/reaction edge SSOT        *)
(* ------------------------------------------------------------------ *)

Definition bondGraphMarker : string := "chem_l0_bond_reaction_graph_v1".
Definition cutGraphMarker : string := "chem_l0_refining_graph_cuts_v1".

Lemma cut_ne_bond_marker :
  cutGraphMarker <> bondGraphMarker.
Proof. discriminate. Qed.

Definition cutNeBondGraph : bool :=
  cutIsSource cutOreWasteFe cut_side_source &&
  negb (cutIsSource cutOreWasteFe cut_side_sink) &&
  refining_cut_role_beq cutRecycleCu.(cut_role_tag) cut_role_recycle_loop &&
  negb (refining_cut_role_beq cut_role_ore_fraction cut_role_waste_tail).

Lemma cut_ne_bond_graph_true : cutNeBondGraph = true.
Proof.
  unfold cutNeBondGraph, cutOreWasteFe, cutRecycleCu.
  reflexivity.
Qed.

Theorem cut_separation_ne_bond_graph :
  cutNeBondGraph = true /\
  cutGraphMarker <> bondGraphMarker.
Proof.
  split.
  - apply cut_ne_bond_graph_true.
  - apply cut_ne_bond_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Path bar — Proved-without-bar fail-closed for cut claims             *)
(* ------------------------------------------------------------------ *)

Inductive cut_path_bar_presence : Type :=
  | cut_bar_absent
  | cut_bar_present.

Record cut_claim_path_bar : Type := {
  cut_bar_presence : cut_path_bar_presence;
  cut_bar_defect_total : nat
}.

Definition cutClaimPathBarAbsent : cut_claim_path_bar :=
  {| cut_bar_presence := cut_bar_absent; cut_bar_defect_total := 0 |}.

Definition cutClaimPathBarZeroDefect : cut_claim_path_bar :=
  {| cut_bar_presence := cut_bar_present; cut_bar_defect_total := 0 |}.

Definition cut_claim_path_bar_zero_defect (b : cut_claim_path_bar) : bool :=
  match cut_bar_presence b with
  | cut_bar_absent => false
  | cut_bar_present => Nat.eqb (cut_bar_defect_total b) 0
  end.

Lemma cut_claim_path_bar_zero_defect_true :
  cut_claim_path_bar_zero_defect cutClaimPathBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma cut_claim_path_bar_absent_not_zero_defect :
  cut_claim_path_bar_zero_defect cutClaimPathBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cut conservation verdict — fail-closed close lattice                 *)
(* ------------------------------------------------------------------ *)

Inductive cut_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_cut_named_ok
  | verdict_trivial_cut_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition cut_conservation_verdict_ok (v : cut_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_cut_named_ok => true
  | _ => false
  end.

Definition cut_conservation_verdict_beq
  (v1 v2 : cut_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_cut_named_ok, verdict_cut_named_ok => true
  | verdict_trivial_cut_refuse, verdict_trivial_cut_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_cut_separation
  (m : CutConservationModality)
  (s : cut_separation)
  (b : cut_claim_path_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : cut_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (cutSeparationNontrivial s)
            then verdict_trivial_cut_refuse
            else if negb (cut_element_z_valid (cut_sep_cut s).(cut_element_z))
                 then verdict_trivial_cut_refuse
                 else
                   match m with
                   | cut_conservation_unwired => verdict_cut_named_ok
                   | cut_conservation_assumed
                   | cut_conservation_surrogate => verdict_unwired_ok
                   | cut_conservation_proved => verdict_proved_without_bar_refuse
                   end.

Definition evaluate_cut_conservation_close
  (m : CutConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : cut_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | cut_conservation_unwired => verdict_unwired_ok
    | cut_conservation_assumed
    | cut_conservation_proved
    | cut_conservation_surrogate => verdict_cut_named_ok
    end.

Definition cut_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_cut_conservation_close
          cut_conservation_proved claim_physics_green claim_production_wired with
  | verdict_cut_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Cut conservation law cells — four laws, open @ Unwired             *)
(* ------------------------------------------------------------------ *)

Inductive cut_conservation_law : Type :=
  | law_cut_named_identity
  | law_trivial_cut_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition cut_conservation_law_count : nat := 4.

Lemma cut_conservation_law_count_is_four :
  cut_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive cut_conservation_law_witness : Type :=
  | cut_law_witness_open
  | cut_law_witness_proved.

Definition evaluate_cut_conservation_law_witness
  (law : cut_conservation_law) (m : CutConservationModality)
  : cut_conservation_law_witness :=
  match m with
  | cut_conservation_unwired
  | cut_conservation_assumed
  | cut_conservation_surrogate => cut_law_witness_open
  | cut_conservation_proved => cut_law_witness_proved
  end.

Lemma all_cut_conservation_laws_open_at_unwired :
  evaluate_cut_conservation_law_witness law_cut_named_identity
    cut_conservation_unwired = cut_law_witness_open /\
  evaluate_cut_conservation_law_witness law_trivial_cut_refuse
    cut_conservation_unwired = cut_law_witness_open /\
  evaluate_cut_conservation_law_witness law_green_invent_refuse
    cut_conservation_unwired = cut_law_witness_open /\
  evaluate_cut_conservation_law_witness law_production_wired_refuse
    cut_conservation_unwired = cut_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  GRAPH-02 pins (structure witnesses — cut laws not Proved)          *)
(* ------------------------------------------------------------------ *)

Definition graph02CutProved : bool := false.

Lemma graph02_cut_proved_false : graph02CutProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_cut_conservation_close
    cut_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_cut_conservation_close
    cut_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  cut_conservation_verdict_ok
    (evaluate_cut_conservation_close
       cut_conservation_unwired false false) =
  true.
Proof.
  unfold cut_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named cut separation close — ore/waste Fe partition conserved       *)
(* ------------------------------------------------------------------ *)

Lemma cut_ore_waste_l1_named_ok :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent false false =
  verdict_cut_named_ok.
Proof. reflexivity. Qed.

Theorem named_ore_waste_cut_conservation :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent false false =
  verdict_cut_named_ok /\
  cutIdentityConserved cutOreWasteFe cutOreWasteFe = true /\
  cutSinkSide cutOreWasteFe = cut_side_sink.
Proof.
  repeat split; reflexivity.
Qed.

Lemma recycle_loop_l1_named_ok :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationRecycleL1
    cutClaimPathBarAbsent false false =
  verdict_cut_named_ok.
Proof. reflexivity. Qed.

Theorem recycle_loop_named_conservation :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationRecycleL1
    cutClaimPathBarAbsent false false =
  verdict_cut_named_ok /\
  recycle_loop_named_vertex = true.
Proof.
  split.
  - apply recycle_loop_l1_named_ok.
  - apply recycle_loop_named_vertex_true.
Qed.

Lemma cut_named_close_ok :
  evaluate_cut_conservation_close
    cut_conservation_proved false false =
  verdict_cut_named_ok.
Proof. reflexivity. Qed.

Theorem named_cut_conservation_close :
  evaluate_cut_conservation_close
    cut_conservation_proved false false =
  verdict_cut_named_ok /\
  cut_conservation_authorized false false = true.
Proof.
  split.
  - apply cut_named_close_ok.
  - unfold cut_conservation_authorized.
    rewrite cut_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial cut fail-closed — cut conservation refuse                   *)
(* ------------------------------------------------------------------ *)

Lemma trivial_cut_refused :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteTrivial
    cutClaimPathBarAbsent false false =
  verdict_trivial_cut_refuse.
Proof. reflexivity. Qed.

Theorem trivial_cut_fail_closed :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteTrivial
    cutClaimPathBarAbsent false false =
  verdict_trivial_cut_refuse /\
  cut_conservation_verdict_ok
    (evaluate_cut_separation
       cut_conservation_unwired cutSeparationOreWasteTrivial
       cutClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_cut_refused.
  - unfold cut_conservation_verdict_ok.
    rewrite trivial_cut_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_cut_conservation_close
    cut_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  cut_conservation_verdict_ok
    (evaluate_cut_conservation_close
       cut_conservation_unwired true false) =
  false.
Proof.
  unfold cut_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_cut_separation_refuse :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — cut conservation refuse            *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  cut_conservation_verdict_ok
    (evaluate_cut_separation
       cut_conservation_unwired cutSeparationOreWasteL1
       cutClaimPathBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold cut_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationRecycleL1
    cutClaimPathBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — cut lattice not production wired          *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_cut_conservation_close
    cut_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  cut_conservation_verdict_ok
    (evaluate_cut_conservation_close
       cut_conservation_proved false true) =
  false.
Proof.
  unfold cut_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cut conservation coherence scaffold — fixture witnesses             *)
(* ------------------------------------------------------------------ *)

Definition cut_conservation_coherence_scaffold : bool :=
  cut_conservation_verdict_beq
    (evaluate_cut_conservation_close
       cut_conservation_proved false false)
    verdict_cut_named_ok &&
  cut_conservation_verdict_beq
    (evaluate_cut_conservation_close
       cut_conservation_unwired true false)
    verdict_green_invent_refuse &&
  cut_conservation_verdict_beq
    (evaluate_cut_conservation_close
       cut_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma cut_conservation_coherence_scaffold_true :
  cut_conservation_coherence_scaffold = true.
Proof.
  unfold cut_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cut_conservation_coherence_scaffold_theorem :
  evaluate_cut_conservation_close
    cut_conservation_proved false false =
    verdict_cut_named_ok /\
  evaluate_cut_conservation_close
    cut_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_cut_conservation_close
    cut_conservation_proved false true =
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
  | claim_cut_conservation.

Definition cut_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition cut_conservation_knowing_fiber_ok : bool :=
  cut_conservation_fiber_ok fiber_quantum_knowing.

Definition cut_conservation_meso_acting_ok : bool :=
  cut_conservation_fiber_ok fiber_meso_acting.

Lemma cut_conservation_knowing_fiber_ok_true :
  cut_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma cut_conservation_meso_acting_not_ok :
  cut_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem cut_conservation_routes_knowing_not_meso :
  cut_conservation_knowing_fiber_ok = true /\
  cut_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply cut_conservation_knowing_fiber_ok_true.
  - apply cut_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  cut_conservation_knowing_fiber_ok &&
  negb cut_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, cut_conservation_knowing_fiber_ok,
    cut_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named cuts + fail-closed + fiber + GRAPH-02      *)
(* ------------------------------------------------------------------ *)

Theorem cut_conservation_fixture_scaffold :
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteL1
    cutClaimPathBarAbsent false false =
    verdict_cut_named_ok /\
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationOreWasteTrivial
    cutClaimPathBarAbsent false false =
    verdict_trivial_cut_refuse /\
  evaluate_cut_separation
    cut_conservation_unwired cutSeparationRecycleL1
    cutClaimPathBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_cut_conservation_close
    cut_conservation_unwired false false =
    verdict_unwired_ok /\
  cut_conservation_knowing_fiber_ok = true /\
  cut_conservation_meso_acting_ok = false /\
  graph02CutProved = false /\
  cutNeBondGraph = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — cut conservation)    *)
(* ------------------------------------------------------------------ *)

Definition refiningGraphCutsAuthority : string :=
  "umst/umst-chem/src/refining_graph_cuts.rs".

Definition chemIntProveGraph02CutsAuthority : string :=
  "CHEM-INT-PROVE-GRAPH-02-CUTS".

Definition refiningGraphCutsMarker : string :=
  "chem_l0_refining_graph_cuts_v1".

Definition cutConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-CUT-CONSERVATION".

Definition cutConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CUT-CONSERVATION GRAPH-02 cut conservation named ore waste partition complement conserved Fe Z=26 Cu Z=29 Og Z=118 recycle loop named trivial cut fail-closed GREEN invent fail-closed proved-without-bar fail-closed graph02CutProved false Unwired cut ne bond geometry knowing quantum fiber not meso acting one axiom second law conservation not second cut axiom not GREEN DFT not physics GREEN not production_wired".

Lemma cut_conservation_cell_id :
  cutConservationCellId = "CHEM-FORMAL-Q-COQ-CUT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma cut_conservation_cites_refining_graph_cuts_rs :
  refiningGraphCutsAuthority <> "".
Proof. discriminate. Qed.

Lemma cut_conservation_cites_int_prove_graph_02_cuts :
  chemIntProveGraph02CutsAuthority = "CHEM-INT-PROVE-GRAPH-02-CUTS".
Proof. reflexivity. Qed.

Lemma cut_conservation_cites_marker :
  refiningGraphCutsMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second cut axiom  *)
(* ------------------------------------------------------------------ *)

Definition cutSecondLawConservationFraming : string :=
  "second_law_conservation_cut_one_axiom_not_second_cut_axiom".

Lemma cut_not_second_cut_axiom :
  cutSecondLawConservationFraming <> "second_cut_axiom".
Proof. discriminate. Qed.

Lemma cut_second_law_conservation_framing :
  cutSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma cut_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma cut_conservation_modality_unwired :
  cutConservationModalityCurrent = cut_conservation_unwired.
Proof. reflexivity. Qed.

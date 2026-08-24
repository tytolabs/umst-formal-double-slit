(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: HyperConservation.v                                   *)
(*                                                                      *)
(*  Knowing-fiber Coq: GRAPH-03 hyper conservation. Multi-constituent *)
(*  ore incidence identity conserved; ternary arity consistent;        *)
(*  hematite ≠ gangue; trivial arity fail-closed; GREEN invent         *)
(*  fail-closed; Proved-without-bar fail-closed; no petgraph fork;     *)
(*  hyper ≠ bond. Geometry routes knowing/quantum fiber not meso       *)
(*  acting. Not 118² GREEN table.                                      *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — hyper conservation is not a second axiom.  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  GRAPH-03 hyper conservation modality (Unwired / Assumed /         *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive HyperConservationModality : Type :=
  | hyper_conservation_unwired
  | hyper_conservation_assumed
  | hyper_conservation_proved
  | hyper_conservation_surrogate.

Definition hyperConservationModalityCurrent : HyperConservationModality :=
  hyper_conservation_unwired.

Definition hyper_lattice_cardinality : nat := 4.

Lemma hyper_lattice_cardinality_is_four :
  hyper_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma hyper_lattice_not_118_squared :
  negb (Nat.eqb hyper_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold hyper_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — hyper element conservation scaffold (not 118² table) *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition hyper_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition hyper_element_iron_z : nat := 26.
Definition hyper_element_copper_z : nat := 29.
Definition hyper_element_oganesson_z : nat := 118.

Lemma hyper_iron_z_is_26 :
  hyper_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma hyper_copper_z_is_29 :
  hyper_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma hyper_oganesson_z_is_118 :
  hyper_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma hyper_fe_cu_z_valid :
  hyper_element_z_valid hyper_element_iron_z = true /\
  hyper_element_z_valid hyper_element_copper_z = true.
Proof.
  split; unfold hyper_element_z_valid, hyper_element_iron_z,
    hyper_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma hyper_oganesson_z_valid :
  hyper_element_z_valid hyper_element_oganesson_z = true.
Proof.
  unfold hyper_element_z_valid, hyper_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ore constituent tags — hematite ≠ gangue @ scaffold                 *)
(* ------------------------------------------------------------------ *)

Inductive ore_constituent : Type :=
  | ore_hematite
  | ore_magnetite
  | ore_silicate_gangue
  | ore_calcite_gangue.

Definition ore_constituent_beq (c1 c2 : ore_constituent) : bool :=
  match c1, c2 with
  | ore_hematite, ore_hematite => true
  | ore_magnetite, ore_magnetite => true
  | ore_silicate_gangue, ore_silicate_gangue => true
  | ore_calcite_gangue, ore_calcite_gangue => true
  | _, _ => false
  end.

Definition ore_constituent_tag (c : ore_constituent) : string :=
  match c with
  | ore_hematite => "hematite"
  | ore_magnetite => "magnetite"
  | ore_silicate_gangue => "silicate_gangue"
  | ore_calcite_gangue => "calcite_gangue"
  end.

Lemma hematite_ne_silicate_gangue_tag :
  ore_constituent_tag ore_hematite <> ore_constituent_tag ore_silicate_gangue.
Proof. discriminate. Qed.

Lemma hematite_ne_gangue :
  ore_constituent_beq ore_hematite ore_silicate_gangue = false /\
  ore_constituent_beq ore_hematite ore_calcite_gangue = false.
Proof. split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Hyperedge arity — ternary / multi-constituent conservation          *)
(* ------------------------------------------------------------------ *)

Inductive hyperedge_arity : Type :=
  | hyper_arity_binary
  | hyper_arity_ternary
  | hyper_arity_multi_constituent.

Definition hyperedge_arity_beq (a1 a2 : hyperedge_arity) : bool :=
  match a1, a2 with
  | hyper_arity_binary, hyper_arity_binary => true
  | hyper_arity_ternary, hyper_arity_ternary => true
  | hyper_arity_multi_constituent, hyper_arity_multi_constituent => true
  | _, _ => false
  end.

Definition hyperedge_arity_min_count (a : hyperedge_arity) : nat :=
  match a with
  | hyper_arity_binary => 2
  | hyper_arity_ternary => 3
  | hyper_arity_multi_constituent => 4
  end.

Definition hyperedge_arity_is_multi (a : hyperedge_arity) : bool :=
  match a with
  | hyper_arity_binary => false
  | hyper_arity_ternary => true
  | hyper_arity_multi_constituent => true
  end.

Lemma ternary_arity_is_multi :
  hyperedge_arity_is_multi hyper_arity_ternary = true.
Proof. reflexivity. Qed.

Lemma binary_arity_not_multi :
  hyperedge_arity_is_multi hyper_arity_binary = false.
Proof. reflexivity. Qed.

Lemma ternary_min_count_is_three :
  hyperedge_arity_min_count hyper_arity_ternary = 3.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Graph topology — multi-head hyperedge ≠ pairwise bond               *)
(* ------------------------------------------------------------------ *)

Inductive graph_topology : Type :=
  | topology_pairwise_bond
  | topology_multi_head_hyperedge.

Definition graph_topology_beq (t1 t2 : graph_topology) : bool :=
  match t1, t2 with
  | topology_pairwise_bond, topology_pairwise_bond => true
  | topology_multi_head_hyperedge, topology_multi_head_hyperedge => true
  | _, _ => false
  end.

Definition graph_topology_is_hyper (t : graph_topology) : bool :=
  match t with
  | topology_pairwise_bond => false
  | topology_multi_head_hyperedge => true
  end.

Lemma multi_head_is_hyper :
  graph_topology_is_hyper topology_multi_head_hyperedge = true.
Proof. reflexivity. Qed.

Lemma pairwise_bond_not_hyper :
  graph_topology_is_hyper topology_pairwise_bond = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Ore hyperedge — multi-constituent incidence identity conserved    *)
(* ------------------------------------------------------------------ *)

Inductive optional_constituent : Type :=
  | head_absent
  | head_present : ore_constituent -> optional_constituent.

Definition optional_constituent_beq (h1 h2 : optional_constituent) : bool :=
  match h1, h2 with
  | head_absent, head_absent => true
  | head_present c1, head_present c2 => ore_constituent_beq c1 c2
  | _, _ => false
  end.

Record ore_hyperedge : Type := {
  hyper_arity_tag : hyperedge_arity;
  hyper_constituent_count : nat;
  hyper_head0 : optional_constituent;
  hyper_head1 : optional_constituent;
  hyper_head2 : optional_constituent;
  hyper_head3 : optional_constituent
}.

Record hyper_incidence : Type := {
  hyper_inc_edge : ore_hyperedge;
  hyper_inc_level : nat
}.

Definition hyperIncidenceNontrivial (h : hyper_incidence) : bool :=
  Nat.ltb 0 (hyper_inc_level h).

Fixpoint count_present_heads (heads : list optional_constituent) : nat :=
  match heads with
  | nil => 0
  | h :: rest =>
      (match h with
       | head_absent => 0
       | head_present _ => 1
       end) + count_present_heads rest
  end.

Definition hyperedge_heads (e : ore_hyperedge) : list optional_constituent :=
  [hyper_head0 e; hyper_head1 e; hyper_head2 e; hyper_head3 e].

Definition hyperArityConsistent (e : ore_hyperedge) : bool :=
  Nat.leb (hyperedge_arity_min_count (hyper_arity_tag e))
    (hyper_constituent_count e) &&
  Nat.eqb (count_present_heads (hyperedge_heads e))
    (hyper_constituent_count e).

Definition hyperIdentityConserved (e1 e2 : ore_hyperedge) : bool :=
  hyperedge_arity_beq e1.(hyper_arity_tag) e2.(hyper_arity_tag) &&
  Nat.eqb e1.(hyper_constituent_count) e2.(hyper_constituent_count) &&
  optional_constituent_beq e1.(hyper_head0) e2.(hyper_head0) &&
  optional_constituent_beq e1.(hyper_head1) e2.(hyper_head1) &&
  optional_constituent_beq e1.(hyper_head2) e2.(hyper_head2) &&
  optional_constituent_beq e1.(hyper_head3) e2.(hyper_head3).

Definition hyperTernaryOre : ore_hyperedge :=
  {| hyper_arity_tag := hyper_arity_ternary;
     hyper_constituent_count := 3;
     hyper_head0 := head_present ore_hematite;
     hyper_head1 := head_present ore_magnetite;
     hyper_head2 := head_present ore_silicate_gangue;
     hyper_head3 := head_absent |}.

Definition hyperMultiOre : ore_hyperedge :=
  {| hyper_arity_tag := hyper_arity_multi_constituent;
     hyper_constituent_count := 4;
     hyper_head0 := head_present ore_hematite;
     hyper_head1 := head_present ore_magnetite;
     hyper_head2 := head_present ore_silicate_gangue;
     hyper_head3 := head_present ore_calcite_gangue |}.

Definition hyperArityBroken : ore_hyperedge :=
  {| hyper_arity_tag := hyper_arity_ternary;
     hyper_constituent_count := 3;
     hyper_head0 := head_present ore_hematite;
     hyper_head1 := head_present ore_magnetite;
     hyper_head2 := head_absent;
     hyper_head3 := head_absent |}.

Definition hyperIncidenceTernaryL1 : hyper_incidence :=
  {| hyper_inc_edge := hyperTernaryOre; hyper_inc_level := 1 |}.

Definition hyperIncidenceMultiL1 : hyper_incidence :=
  {| hyper_inc_edge := hyperMultiOre; hyper_inc_level := 1 |}.

Definition hyperIncidenceTrivial : hyper_incidence :=
  {| hyper_inc_edge := hyperTernaryOre; hyper_inc_level := 0 |}.

Definition hyperIncidenceArityBroken : hyper_incidence :=
  {| hyper_inc_edge := hyperArityBroken; hyper_inc_level := 1 |}.

Lemma hyper_ternary_ore_arity_consistent :
  hyperArityConsistent hyperTernaryOre = true.
Proof. reflexivity. Qed.

Lemma hyper_multi_ore_arity_consistent :
  hyperArityConsistent hyperMultiOre = true.
Proof. reflexivity. Qed.

Lemma hyper_arity_broken_not_consistent :
  hyperArityConsistent hyperArityBroken = false.
Proof. reflexivity. Qed.

Lemma hyper_ternary_incidence_nontrivial :
  hyperIncidenceNontrivial hyperIncidenceTernaryL1 = true.
Proof. reflexivity. Qed.

Lemma hyper_ternary_identity_conserved :
  hyperIdentityConserved hyperTernaryOre hyperTernaryOre = true.
Proof. reflexivity. Qed.

Lemma hyper_ternary_hematite_present :
  optional_constituent_beq (hyper_head0 hyperTernaryOre)
    (head_present ore_hematite) = true.
Proof. reflexivity. Qed.

Lemma hyper_ternary_gangue_present :
  optional_constituent_beq (hyper_head2 hyperTernaryOre)
    (head_present ore_silicate_gangue) = true.
Proof. reflexivity. Qed.

Lemma hyper_trivial_not_nontrivial :
  hyperIncidenceNontrivial hyperIncidenceTrivial = false.
Proof. reflexivity. Qed.

Definition multi_constituent_named_vertex : bool :=
  hyperedge_arity_is_multi (hyper_arity_tag hyperTernaryOre).

Lemma multi_constituent_named_vertex_true :
  multi_constituent_named_vertex = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  No petgraph fork — hyper conservation refuse kernel fork            *)
(* ------------------------------------------------------------------ *)

Definition petgraphKernelForked : bool := false.

Lemma petgraph_kernel_not_forked :
  petgraphKernelForked = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Hyper ≠ bond — incidence morphisms not bond/reaction edge SSOT       *)
(* ------------------------------------------------------------------ *)

Definition bondGraphMarker : string := "chem_l0_bond_reaction_graph_v1".
Definition hyperGraphMarker : string := "chem_l0_ore_hypergraph_v1".

Lemma hyper_ne_bond_marker :
  hyperGraphMarker <> bondGraphMarker.
Proof. discriminate. Qed.

Definition hyperNeBondGraph : bool :=
  graph_topology_is_hyper topology_multi_head_hyperedge &&
  negb (graph_topology_is_hyper topology_pairwise_bond) &&
  hyperArityConsistent hyperTernaryOre &&
  negb (ore_constituent_beq ore_hematite ore_silicate_gangue).

Lemma hyper_ne_bond_graph_true : hyperNeBondGraph = true.
Proof.
  unfold hyperNeBondGraph.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem hyper_incidence_ne_bond_graph :
  hyperNeBondGraph = true /\
  hyperGraphMarker <> bondGraphMarker.
Proof.
  split.
  - apply hyper_ne_bond_graph_true.
  - apply hyper_ne_bond_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Path bar — Proved-without-bar fail-closed for hyper claims           *)
(* ------------------------------------------------------------------ *)

Inductive hyper_path_bar_presence : Type :=
  | hyper_bar_absent
  | hyper_bar_present.

Record hyper_claim_path_bar : Type := {
  hyper_bar_presence : hyper_path_bar_presence;
  hyper_bar_defect_total : nat
}.

Definition hyperClaimPathBarAbsent : hyper_claim_path_bar :=
  {| hyper_bar_presence := hyper_bar_absent; hyper_bar_defect_total := 0 |}.

Definition hyperClaimPathBarZeroDefect : hyper_claim_path_bar :=
  {| hyper_bar_presence := hyper_bar_present; hyper_bar_defect_total := 0 |}.

Definition hyper_claim_path_bar_zero_defect (b : hyper_claim_path_bar) : bool :=
  match hyper_bar_presence b with
  | hyper_bar_absent => false
  | hyper_bar_present => Nat.eqb (hyper_bar_defect_total b) 0
  end.

Lemma hyper_claim_path_bar_zero_defect_true :
  hyper_claim_path_bar_zero_defect hyperClaimPathBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma hyper_claim_path_bar_absent_not_zero_defect :
  hyper_claim_path_bar_zero_defect hyperClaimPathBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Hyper conservation verdict — fail-closed close lattice               *)
(* ------------------------------------------------------------------ *)

Inductive hyper_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_incidence_named_ok
  | verdict_trivial_hyper_refuse
  | verdict_arity_inconsistent_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition hyper_conservation_verdict_ok (v : hyper_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_incidence_named_ok => true
  | _ => false
  end.

Definition hyper_conservation_verdict_beq
  (v1 v2 : hyper_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_incidence_named_ok, verdict_incidence_named_ok => true
  | verdict_trivial_hyper_refuse, verdict_trivial_hyper_refuse => true
  | verdict_arity_inconsistent_refuse, verdict_arity_inconsistent_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_hyper_incidence
  (m : HyperConservationModality)
  (h : hyper_incidence)
  (b : hyper_claim_path_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : hyper_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (hyperIncidenceNontrivial h)
            then verdict_trivial_hyper_refuse
            else if negb (hyperArityConsistent (hyper_inc_edge h))
                 then verdict_arity_inconsistent_refuse
                 else
                   match m with
                   | hyper_conservation_unwired => verdict_incidence_named_ok
                   | hyper_conservation_assumed
                   | hyper_conservation_surrogate => verdict_unwired_ok
                   | hyper_conservation_proved => verdict_proved_without_bar_refuse
                   end.

Definition evaluate_hyper_conservation_close
  (m : HyperConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : hyper_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | hyper_conservation_unwired => verdict_unwired_ok
    | hyper_conservation_assumed
    | hyper_conservation_proved
    | hyper_conservation_surrogate => verdict_incidence_named_ok
    end.

Definition hyper_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_hyper_conservation_close
          hyper_conservation_proved claim_physics_green claim_production_wired with
  | verdict_incidence_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Hyper conservation law cells — four laws, open @ Unwired             *)
(* ------------------------------------------------------------------ *)

Inductive hyper_conservation_law : Type :=
  | law_hyper_incidence_named
  | law_arity_inconsistent_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition hyper_conservation_law_count : nat := 4.

Lemma hyper_conservation_law_count_is_four :
  hyper_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive hyper_conservation_law_witness : Type :=
  | hyper_law_witness_open
  | hyper_law_witness_proved.

Definition evaluate_hyper_conservation_law_witness
  (law : hyper_conservation_law) (m : HyperConservationModality)
  : hyper_conservation_law_witness :=
  match m with
  | hyper_conservation_unwired
  | hyper_conservation_assumed
  | hyper_conservation_surrogate => hyper_law_witness_open
  | hyper_conservation_proved => hyper_law_witness_proved
  end.

Lemma all_hyper_conservation_laws_open_at_unwired :
  evaluate_hyper_conservation_law_witness law_hyper_incidence_named
    hyper_conservation_unwired = hyper_law_witness_open /\
  evaluate_hyper_conservation_law_witness law_arity_inconsistent_refuse
    hyper_conservation_unwired = hyper_law_witness_open /\
  evaluate_hyper_conservation_law_witness law_green_invent_refuse
    hyper_conservation_unwired = hyper_law_witness_open /\
  evaluate_hyper_conservation_law_witness law_production_wired_refuse
    hyper_conservation_unwired = hyper_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  GRAPH-03 pins (structure witnesses — hyper laws not Proved)        *)
(* ------------------------------------------------------------------ *)

Definition graph03HyperProved : bool := false.

Lemma graph03_hyper_proved_false : graph03HyperProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_hyper_conservation_close
    hyper_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_hyper_conservation_close
    hyper_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  hyper_conservation_verdict_ok
    (evaluate_hyper_conservation_close
       hyper_conservation_unwired false false) =
  true.
Proof.
  unfold hyper_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named hyper incidence close — ternary ore partition conserved     *)
(* ------------------------------------------------------------------ *)

Lemma hyper_ternary_l1_named_ok :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent false false =
  verdict_incidence_named_ok.
Proof. reflexivity. Qed.

Theorem named_ternary_hyper_conservation :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent false false =
  verdict_incidence_named_ok /\
  hyperIdentityConserved hyperTernaryOre hyperTernaryOre = true /\
  hyperArityConsistent hyperTernaryOre = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma hyper_multi_l1_named_ok :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceMultiL1
    hyperClaimPathBarAbsent false false =
  verdict_incidence_named_ok.
Proof. reflexivity. Qed.

Theorem multi_constituent_hyper_conservation :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceMultiL1
    hyperClaimPathBarAbsent false false =
  verdict_incidence_named_ok /\
  multi_constituent_named_vertex = true.
Proof.
  split.
  - apply hyper_multi_l1_named_ok.
  - apply multi_constituent_named_vertex_true.
Qed.

Lemma hyper_named_close_ok :
  evaluate_hyper_conservation_close
    hyper_conservation_proved false false =
  verdict_incidence_named_ok.
Proof. reflexivity. Qed.

Theorem named_hyper_conservation_close :
  evaluate_hyper_conservation_close
    hyper_conservation_proved false false =
  verdict_incidence_named_ok /\
  hyper_conservation_authorized false false = true.
Proof.
  split.
  - apply hyper_named_close_ok.
  - unfold hyper_conservation_authorized.
    rewrite hyper_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial hyper fail-closed — hyper conservation refuse               *)
(* ------------------------------------------------------------------ *)

Lemma trivial_hyper_refused :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTrivial
    hyperClaimPathBarAbsent false false =
  verdict_trivial_hyper_refuse.
Proof. reflexivity. Qed.

Theorem trivial_hyper_fail_closed :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTrivial
    hyperClaimPathBarAbsent false false =
  verdict_trivial_hyper_refuse /\
  hyper_conservation_verdict_ok
    (evaluate_hyper_incidence
       hyper_conservation_unwired hyperIncidenceTrivial
       hyperClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_hyper_refused.
  - unfold hyper_conservation_verdict_ok.
    rewrite trivial_hyper_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Arity inconsistent fail-closed — hyper conservation refuse          *)
(* ------------------------------------------------------------------ *)

Lemma arity_inconsistent_refused :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceArityBroken
    hyperClaimPathBarAbsent false false =
  verdict_arity_inconsistent_refuse.
Proof. reflexivity. Qed.

Theorem arity_inconsistent_fail_closed :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceArityBroken
    hyperClaimPathBarAbsent false false =
  verdict_arity_inconsistent_refuse /\
  hyper_conservation_verdict_ok
    (evaluate_hyper_incidence
       hyper_conservation_unwired hyperIncidenceArityBroken
       hyperClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply arity_inconsistent_refused.
  - unfold hyper_conservation_verdict_ok.
    rewrite arity_inconsistent_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_hyper_conservation_close
    hyper_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  hyper_conservation_verdict_ok
    (evaluate_hyper_conservation_close
       hyper_conservation_unwired true false) =
  false.
Proof.
  unfold hyper_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_hyper_incidence_refuse :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — hyper conservation refuse          *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  hyper_conservation_verdict_ok
    (evaluate_hyper_incidence
       hyper_conservation_unwired hyperIncidenceTernaryL1
       hyperClaimPathBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold hyper_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceMultiL1
    hyperClaimPathBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — hyper lattice not production wired        *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_hyper_conservation_close
    hyper_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  hyper_conservation_verdict_ok
    (evaluate_hyper_conservation_close
       hyper_conservation_proved false true) =
  false.
Proof.
  unfold hyper_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Hyper conservation coherence scaffold — fixture witnesses             *)
(* ------------------------------------------------------------------ *)

Definition hyper_conservation_coherence_scaffold : bool :=
  hyper_conservation_verdict_beq
    (evaluate_hyper_conservation_close
       hyper_conservation_proved false false)
    verdict_incidence_named_ok &&
  hyper_conservation_verdict_beq
    (evaluate_hyper_conservation_close
       hyper_conservation_unwired true false)
    verdict_green_invent_refuse &&
  hyper_conservation_verdict_beq
    (evaluate_hyper_conservation_close
       hyper_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma hyper_conservation_coherence_scaffold_true :
  hyper_conservation_coherence_scaffold = true.
Proof.
  unfold hyper_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem hyper_conservation_coherence_scaffold_theorem :
  evaluate_hyper_conservation_close
    hyper_conservation_proved false false =
    verdict_incidence_named_ok /\
  evaluate_hyper_conservation_close
    hyper_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_hyper_conservation_close
    hyper_conservation_proved false true =
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
  | claim_hyper_conservation.

Definition hyper_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition hyper_conservation_knowing_fiber_ok : bool :=
  hyper_conservation_fiber_ok fiber_quantum_knowing.

Definition hyper_conservation_meso_acting_ok : bool :=
  hyper_conservation_fiber_ok fiber_meso_acting.

Lemma hyper_conservation_knowing_fiber_ok_true :
  hyper_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma hyper_conservation_meso_acting_not_ok :
  hyper_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem hyper_conservation_routes_knowing_not_meso :
  hyper_conservation_knowing_fiber_ok = true /\
  hyper_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply hyper_conservation_knowing_fiber_ok_true.
  - apply hyper_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  hyper_conservation_knowing_fiber_ok &&
  negb hyper_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, hyper_conservation_knowing_fiber_ok,
    hyper_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named hyper + fail-closed + fiber + GRAPH-03   *)
(* ------------------------------------------------------------------ *)

Theorem hyper_conservation_fixture_scaffold :
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTernaryL1
    hyperClaimPathBarAbsent false false =
    verdict_incidence_named_ok /\
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceTrivial
    hyperClaimPathBarAbsent false false =
    verdict_trivial_hyper_refuse /\
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceArityBroken
    hyperClaimPathBarAbsent false false =
    verdict_arity_inconsistent_refuse /\
  evaluate_hyper_incidence
    hyper_conservation_unwired hyperIncidenceMultiL1
    hyperClaimPathBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_hyper_conservation_close
    hyper_conservation_unwired false false =
    verdict_unwired_ok /\
  hyper_conservation_knowing_fiber_ok = true /\
  hyper_conservation_meso_acting_ok = false /\
  graph03HyperProved = false /\
  hyperNeBondGraph = true /\
  petgraphKernelForked = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — hyper conservation)  *)
(* ------------------------------------------------------------------ *)

Definition oreHypergraphAuthority : string :=
  "umst/umst-chem/src/ore_hypergraph.rs".

Definition chemIntProveGraph03HyperAuthority : string :=
  "CHEM-INT-PROVE-GRAPH-03-HYPER".

Definition oreHypergraphMarker : string :=
  "chem_l0_ore_hypergraph_v1".

Definition hyperConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-HYPER-CONSERVATION".

Definition hyperConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-HYPER-CONSERVATION GRAPH-03 hyper conservation multi-constituent ore incidence identity conserved ternary arity consistent hematite ne gangue trivial hyper fail-closed GREEN invent fail-closed proved-without-bar fail-closed graph03HyperProved false Unwired hyper ne bond no petgraph fork geometry knowing quantum fiber not meso acting one axiom second law conservation not second hyper axiom not GREEN DFT not physics GREEN not production_wired".

Lemma hyper_conservation_cell_id :
  hyperConservationCellId = "CHEM-FORMAL-Q-COQ-HYPER-CONSERVATION".
Proof. reflexivity. Qed.

Lemma hyper_conservation_cites_ore_hypergraph_rs :
  oreHypergraphAuthority <> "".
Proof. discriminate. Qed.

Lemma hyper_conservation_cites_int_prove_graph_03_hyper :
  chemIntProveGraph03HyperAuthority = "CHEM-INT-PROVE-GRAPH-03-HYPER".
Proof. reflexivity. Qed.

Lemma hyper_conservation_cites_marker :
  oreHypergraphMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second hyper axiom  *)
(* ------------------------------------------------------------------ *)

Definition hyperSecondLawConservationFraming : string :=
  "second_law_conservation_hyper_one_axiom_not_second_hyper_axiom".

Lemma hyper_not_second_hyper_axiom :
  hyperSecondLawConservationFraming <> "second_hyper_axiom".
Proof. discriminate. Qed.

Lemma hyper_second_law_conservation_framing :
  hyperSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma hyper_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma hyper_conservation_modality_unwired :
  hyperConservationModalityCurrent = hyper_conservation_unwired.
Proof. reflexivity. Qed.

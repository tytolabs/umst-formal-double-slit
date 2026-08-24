(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: DissipConservation.v                                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: GRAPH-04 dissip conservation. Cyclic vs       *)
(*  dissipative path identity conserved; reaction-cycle closed;        *)
(*  bond-path dissipative typed; cycle ne dissipative kind; trivial    *)
(*  path fail-closed; GREEN invent fail-closed; Proved-without-bar     *)
(*  fail-closed. Geometry routes knowing/quantum fiber not meso        *)
(*  acting. Not 118² GREEN table.                                      *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — dissip conservation is not a second axiom. *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  GRAPH-04 dissip conservation modality (Unwired / Assumed /        *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive DissipConservationModality : Type :=
  | dissip_conservation_unwired
  | dissip_conservation_assumed
  | dissip_conservation_proved
  | dissip_conservation_surrogate.

Definition dissipConservationModalityCurrent : DissipConservationModality :=
  dissip_conservation_unwired.

Definition dissip_lattice_cardinality : nat := 4.

Lemma dissip_lattice_cardinality_is_four :
  dissip_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma dissip_lattice_not_118_squared :
  negb (Nat.eqb dissip_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold dissip_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — dissip element conservation scaffold (not 118²)    *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition dissip_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition dissip_element_iron_z : nat := 26.
Definition dissip_element_copper_z : nat := 29.
Definition dissip_element_oganesson_z : nat := 118.

Lemma dissip_iron_z_is_26 :
  dissip_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma dissip_copper_z_is_29 :
  dissip_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma dissip_oganesson_z_is_118 :
  dissip_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma dissip_fe_cu_z_valid :
  dissip_element_z_valid dissip_element_iron_z = true /\
  dissip_element_z_valid dissip_element_copper_z = true.
Proof.
  split; unfold dissip_element_z_valid, dissip_element_iron_z,
    dissip_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma dissip_oganesson_z_valid :
  dissip_element_z_valid dissip_element_oganesson_z = true.
Proof.
  unfold dissip_element_z_valid, dissip_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Path kind — cyclic vs dissipative; cycle ne dissipative kind        *)
(* ------------------------------------------------------------------ *)

Inductive path_kind : Type :=
  | path_kind_cyclic
  | path_kind_dissipative.

Definition path_kind_beq (k1 k2 : path_kind) : bool :=
  match k1, k2 with
  | path_kind_cyclic, path_kind_cyclic => true
  | path_kind_dissipative, path_kind_dissipative => true
  | _, _ => false
  end.

Definition path_kind_is_cyclic (k : path_kind) : bool :=
  match k with
  | path_kind_cyclic => true
  | path_kind_dissipative => false
  end.

Definition path_kind_is_dissipative (k : path_kind) : bool :=
  match k with
  | path_kind_cyclic => false
  | path_kind_dissipative => true
  end.

Lemma cyclic_path_kind_is_cyclic :
  path_kind_is_cyclic path_kind_cyclic = true.
Proof. reflexivity. Qed.

Lemma dissipative_path_kind_is_dissipative :
  path_kind_is_dissipative path_kind_dissipative = true.
Proof. reflexivity. Qed.

Lemma cyclic_not_dissipative_kind :
  path_kind_is_cyclic path_kind_cyclic = true /\
  path_kind_is_dissipative path_kind_cyclic = false.
Proof. split; reflexivity. Qed.

Lemma dissipative_not_cyclic_kind :
  path_kind_is_dissipative path_kind_dissipative = true /\
  path_kind_is_cyclic path_kind_dissipative = false.
Proof. split; reflexivity. Qed.

Lemma cycle_ne_dissipative_kind :
  path_kind_beq path_kind_cyclic path_kind_dissipative = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Reaction cycle — closed loop scaffold                               *)
(* ------------------------------------------------------------------ *)

Record reaction_cycle_vertex : Type := {
  cycle_vertex_id : nat;
  cycle_vertex_z : nat
}.

Definition reactionCycleVertex (id z : nat) : reaction_cycle_vertex :=
  {| cycle_vertex_id := id; cycle_vertex_z := z |}.

Record reaction_cycle : Type := {
  cycle_start : reaction_cycle_vertex;
  cycle_end : reaction_cycle_vertex;
  cycle_hop_count : nat;
  cycle_path_kind : path_kind
}.

Definition reactionCycleClosed (c : reaction_cycle) : bool :=
  Nat.eqb (cycle_start c).(cycle_vertex_id)
    (cycle_end c).(cycle_vertex_id) &&
  Nat.eqb (cycle_start c).(cycle_vertex_z)
    (cycle_end c).(cycle_vertex_z).

Definition reactionCycleNontrivial (c : reaction_cycle) : bool :=
  Nat.ltb 0 (cycle_hop_count c).

Definition reactionCycleIdentityConserved (c1 c2 : reaction_cycle) : bool :=
  path_kind_beq c1.(cycle_path_kind) c2.(cycle_path_kind) &&
  Nat.eqb c1.(cycle_hop_count) c2.(cycle_hop_count) &&
  Nat.eqb (cycle_start c1).(cycle_vertex_id)
    (cycle_start c2).(cycle_vertex_id) &&
  Nat.eqb (cycle_start c1).(cycle_vertex_z)
    (cycle_start c2).(cycle_vertex_z) &&
  Nat.eqb (cycle_end c1).(cycle_vertex_id)
    (cycle_end c2).(cycle_vertex_id) &&
  Nat.eqb (cycle_end c1).(cycle_vertex_z)
    (cycle_end c2).(cycle_vertex_z).

Definition reactionCycleFeCuClosed : reaction_cycle :=
  let v := reactionCycleVertex 1 dissip_element_iron_z in
  {| cycle_start := v;
     cycle_end := v;
     cycle_hop_count := 3;
     cycle_path_kind := path_kind_cyclic |}.

Definition reactionCycleDissipativeOpen : reaction_cycle :=
  {| cycle_start := reactionCycleVertex 1 dissip_element_iron_z;
     cycle_end := reactionCycleVertex 2 dissip_element_copper_z;
     cycle_hop_count := 2;
     cycle_path_kind := path_kind_dissipative |}.

Definition reactionCycleTrivial : reaction_cycle :=
  {| cycle_start := reactionCycleVertex 0 0;
     cycle_end := reactionCycleVertex 0 0;
     cycle_hop_count := 0;
     cycle_path_kind := path_kind_cyclic |}.

Definition reactionCycleBroken : reaction_cycle :=
  {| cycle_start := reactionCycleVertex 1 dissip_element_iron_z;
     cycle_end := reactionCycleVertex 1 dissip_element_copper_z;
     cycle_hop_count := 3;
     cycle_path_kind := path_kind_cyclic |}.

Lemma reaction_cycle_fe_cu_closed :
  reactionCycleClosed reactionCycleFeCuClosed = true.
Proof. reflexivity. Qed.

Lemma reaction_cycle_dissipative_not_closed :
  reactionCycleClosed reactionCycleDissipativeOpen = false.
Proof. reflexivity. Qed.

Lemma reaction_cycle_fe_cu_nontrivial :
  reactionCycleNontrivial reactionCycleFeCuClosed = true.
Proof. reflexivity. Qed.

Lemma reaction_cycle_trivial_not_nontrivial :
  reactionCycleNontrivial reactionCycleTrivial = false.
Proof. reflexivity. Qed.

Lemma reaction_cycle_broken_not_closed :
  reactionCycleClosed reactionCycleBroken = false.
Proof. reflexivity. Qed.

Lemma reaction_cycle_fe_cu_identity_conserved :
  reactionCycleIdentityConserved reactionCycleFeCuClosed
    reactionCycleFeCuClosed = true.
Proof. reflexivity. Qed.

Lemma reaction_cycle_cyclic_kind :
  path_kind_is_cyclic (cycle_path_kind reactionCycleFeCuClosed) = true.
Proof. reflexivity. Qed.

Lemma reaction_cycle_dissipative_kind :
  path_kind_is_dissipative (cycle_path_kind reactionCycleDissipativeOpen) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Bond-path — dissipative typed scaffold                              *)
(* ------------------------------------------------------------------ *)

Record bond_path_dissipation_witness : Type := {
  bond_path_dissipation_microjoules : nat
}.

Definition bondPathDissipationZero : bond_path_dissipation_witness :=
  {| bond_path_dissipation_microjoules := 0 |}.

Definition bondPathDissipationPositive : bond_path_dissipation_witness :=
  {| bond_path_dissipation_microjoules := 1 |}.

Definition bond_path_dissipation_positive (w : bond_path_dissipation_witness) : bool :=
  Nat.ltb 0 (bond_path_dissipation_microjoules w).

Record bond_path : Type := {
  bond_path_from : nat;
  bond_path_to : nat;
  bond_path_from_z : nat;
  bond_path_to_z : nat;
  bond_path_kind_tag : path_kind;
  bond_path_dissipation : bond_path_dissipation_witness
}.

Definition bondPathNontrivial (p : bond_path) : bool :=
  negb (Nat.eqb (bond_path_from p) (bond_path_to p)).

Definition bondPathDissipativeTyped (p : bond_path) : bool :=
  path_kind_is_dissipative (bond_path_kind_tag p) &&
  bond_path_dissipation_positive (bond_path_dissipation p).

Definition bondPathIdentityConserved (p1 p2 : bond_path) : bool :=
  Nat.eqb (bond_path_from p1) (bond_path_from p2) &&
  Nat.eqb (bond_path_to p1) (bond_path_to p2) &&
  Nat.eqb p1.(bond_path_from_z) p2.(bond_path_from_z) &&
  Nat.eqb p1.(bond_path_to_z) p2.(bond_path_to_z) &&
  path_kind_beq p1.(bond_path_kind_tag) p2.(bond_path_kind_tag) &&
  Nat.eqb (bond_path_dissipation_microjoules (bond_path_dissipation p1))
    (bond_path_dissipation_microjoules (bond_path_dissipation p2)).

Definition bondPathFeCuDissipativeTyped : bond_path :=
  {| bond_path_from := 1;
     bond_path_to := 2;
     bond_path_from_z := dissip_element_iron_z;
     bond_path_to_z := dissip_element_copper_z;
     bond_path_kind_tag := path_kind_dissipative;
     bond_path_dissipation := bondPathDissipationPositive |}.

Definition bondPathCyclicUntyped : bond_path :=
  {| bond_path_from := 1;
     bond_path_to := 3;
     bond_path_from_z := dissip_element_iron_z;
     bond_path_to_z := dissip_element_oganesson_z;
     bond_path_kind_tag := path_kind_cyclic;
     bond_path_dissipation := bondPathDissipationZero |}.

Definition bondPathSelfLoop : bond_path :=
  {| bond_path_from := 3;
     bond_path_to := 3;
     bond_path_from_z := dissip_element_oganesson_z;
     bond_path_to_z := dissip_element_oganesson_z;
     bond_path_kind_tag := path_kind_dissipative;
     bond_path_dissipation := bondPathDissipationPositive |}.

Definition bondPathDissipativeZeroWitness : bond_path :=
  {| bond_path_from := 1;
     bond_path_to := 2;
     bond_path_from_z := dissip_element_iron_z;
     bond_path_to_z := dissip_element_copper_z;
     bond_path_kind_tag := path_kind_dissipative;
     bond_path_dissipation := bondPathDissipationZero |}.

Lemma bond_path_fe_cu_dissipative_typed :
  bondPathDissipativeTyped bondPathFeCuDissipativeTyped = true.
Proof. reflexivity. Qed.

Lemma bond_path_cyclic_not_dissipative_typed :
  bondPathDissipativeTyped bondPathCyclicUntyped = false.
Proof. reflexivity. Qed.

Lemma bond_path_fe_cu_nontrivial :
  bondPathNontrivial bondPathFeCuDissipativeTyped = true.
Proof. reflexivity. Qed.

Lemma bond_path_self_loop_not_nontrivial :
  bondPathNontrivial bondPathSelfLoop = false.
Proof. reflexivity. Qed.

Lemma bond_path_dissipative_zero_witness_not_typed :
  bondPathDissipativeTyped bondPathDissipativeZeroWitness = false.
Proof. reflexivity. Qed.

Lemma bond_path_fe_cu_identity_conserved :
  bondPathIdentityConserved bondPathFeCuDissipativeTyped
    bondPathFeCuDissipativeTyped = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Dissip incidence — cyclic vs dissipative path identity conserved  *)
(* ------------------------------------------------------------------ *)

Record dissip_incidence : Type := {
  dissip_inc_cycle : reaction_cycle;
  dissip_inc_bond_path : bond_path;
  dissip_inc_level : nat
}.

Definition dissipIncidenceNontrivial (h : dissip_incidence) : bool :=
  Nat.ltb 0 (dissip_inc_level h).

Definition dissipPathKindConsistent (h : dissip_incidence) : bool :=
  path_kind_beq (cycle_path_kind (dissip_inc_cycle h))
    (bond_path_kind_tag (dissip_inc_bond_path h)).

Definition dissipIncidenceFeCuCyclicL1 : dissip_incidence :=
  {| dissip_inc_cycle := reactionCycleFeCuClosed;
     dissip_inc_bond_path := bondPathCyclicUntyped;
     dissip_inc_level := 1 |}.

Definition dissipIncidenceFeCuDissipativeL1 : dissip_incidence :=
  {| dissip_inc_cycle := reactionCycleDissipativeOpen;
     dissip_inc_bond_path := bondPathFeCuDissipativeTyped;
     dissip_inc_level := 1 |}.

Definition dissipIncidenceTrivial : dissip_incidence :=
  {| dissip_inc_cycle := reactionCycleTrivial;
     dissip_inc_bond_path := bondPathCyclicUntyped;
     dissip_inc_level := 0 |}.

Definition dissipIncidenceCycleBroken : dissip_incidence :=
  {| dissip_inc_cycle := reactionCycleBroken;
     dissip_inc_bond_path := bondPathCyclicUntyped;
     dissip_inc_level := 1 |}.

Definition dissipIncidenceKindMismatch : dissip_incidence :=
  {| dissip_inc_cycle := reactionCycleFeCuClosed;
     dissip_inc_bond_path := bondPathFeCuDissipativeTyped;
     dissip_inc_level := 1 |}.

Lemma dissip_incidence_fe_cu_cyclic_consistent :
  dissipPathKindConsistent dissipIncidenceFeCuCyclicL1 = true.
Proof. reflexivity. Qed.

Lemma dissip_incidence_fe_cu_dissipative_consistent :
  dissipPathKindConsistent dissipIncidenceFeCuDissipativeL1 = true.
Proof. reflexivity. Qed.

Lemma dissip_incidence_kind_mismatch_not_consistent :
  dissipPathKindConsistent dissipIncidenceKindMismatch = false.
Proof. reflexivity. Qed.

Lemma dissip_incidence_fe_cu_nontrivial :
  dissipIncidenceNontrivial dissipIncidenceFeCuCyclicL1 = true.
Proof. reflexivity. Qed.

Lemma dissip_incidence_trivial_not_nontrivial :
  dissipIncidenceNontrivial dissipIncidenceTrivial = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cycle ne dissipative — path morphisms not interchangeable           *)
(* ------------------------------------------------------------------ *)

Definition cyclicPathMarker : string := "chem_l0_reaction_cycle_v1".
Definition dissipativePathMarker : string := "chem_l0_bond_path_dissipative_v1".

Lemma cycle_ne_dissipative_marker :
  cyclicPathMarker <> dissipativePathMarker.
Proof. discriminate. Qed.

Definition cycleNeDissipativePath : bool :=
  path_kind_is_cyclic path_kind_cyclic &&
  path_kind_is_dissipative path_kind_dissipative &&
  negb (path_kind_beq path_kind_cyclic path_kind_dissipative) &&
  reactionCycleClosed reactionCycleFeCuClosed &&
  bondPathDissipativeTyped bondPathFeCuDissipativeTyped.

Lemma cycle_ne_dissipative_path_true : cycleNeDissipativePath = true.
Proof.
  unfold cycleNeDissipativePath.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cycle_ne_dissipative_path_identity :
  cycleNeDissipativePath = true /\
  cyclicPathMarker <> dissipativePathMarker.
Proof.
  split.
  - apply cycle_ne_dissipative_path_true.
  - apply cycle_ne_dissipative_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Path bar — Proved-without-bar fail-closed for dissip claims          *)
(* ------------------------------------------------------------------ *)

Inductive dissip_path_bar_presence : Type :=
  | dissip_bar_absent
  | dissip_bar_present.

Record dissip_claim_path_bar : Type := {
  dissip_bar_presence : dissip_path_bar_presence;
  dissip_bar_defect_total : nat
}.

Definition dissipClaimPathBarAbsent : dissip_claim_path_bar :=
  {| dissip_bar_presence := dissip_bar_absent; dissip_bar_defect_total := 0 |}.

Definition dissipClaimPathBarZeroDefect : dissip_claim_path_bar :=
  {| dissip_bar_presence := dissip_bar_present; dissip_bar_defect_total := 0 |}.

Definition dissip_claim_path_bar_zero_defect (b : dissip_claim_path_bar) : bool :=
  match dissip_bar_presence b with
  | dissip_bar_absent => false
  | dissip_bar_present => Nat.eqb (dissip_bar_defect_total b) 0
  end.

Lemma dissip_claim_path_bar_zero_defect_true :
  dissip_claim_path_bar_zero_defect dissipClaimPathBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma dissip_claim_path_bar_absent_not_zero_defect :
  dissip_claim_path_bar_zero_defect dissipClaimPathBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Dissip conservation verdict — fail-closed close lattice             *)
(* ------------------------------------------------------------------ *)

Inductive dissip_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_path_named_ok
  | verdict_trivial_dissip_refuse
  | verdict_cycle_open_refuse
  | verdict_kind_mismatch_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition dissip_conservation_verdict_ok (v : dissip_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_path_named_ok => true
  | _ => false
  end.

Definition dissip_conservation_verdict_beq
  (v1 v2 : dissip_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_path_named_ok, verdict_path_named_ok => true
  | verdict_trivial_dissip_refuse, verdict_trivial_dissip_refuse => true
  | verdict_cycle_open_refuse, verdict_cycle_open_refuse => true
  | verdict_kind_mismatch_refuse, verdict_kind_mismatch_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_dissip_incidence
  (m : DissipConservationModality)
  (h : dissip_incidence)
  (b : dissip_claim_path_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : dissip_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (dissipIncidenceNontrivial h)
            then verdict_trivial_dissip_refuse
            else if path_kind_is_cyclic (cycle_path_kind (dissip_inc_cycle h)) &&
                  negb (reactionCycleClosed (dissip_inc_cycle h))
                 then verdict_cycle_open_refuse
                 else if negb (dissipPathKindConsistent h)
                      then verdict_kind_mismatch_refuse
                      else
                        match m with
                        | dissip_conservation_unwired => verdict_path_named_ok
                        | dissip_conservation_assumed
                        | dissip_conservation_surrogate => verdict_unwired_ok
                        | dissip_conservation_proved => verdict_proved_without_bar_refuse
                        end.

Definition evaluate_dissip_conservation_close
  (m : DissipConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : dissip_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | dissip_conservation_unwired => verdict_unwired_ok
    | dissip_conservation_assumed
    | dissip_conservation_proved
    | dissip_conservation_surrogate => verdict_path_named_ok
    end.

Definition dissip_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_dissip_conservation_close
          dissip_conservation_proved claim_physics_green claim_production_wired with
  | verdict_path_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Dissip conservation law cells — four laws, open @ Unwired           *)
(* ------------------------------------------------------------------ *)

Inductive dissip_conservation_law : Type :=
  | law_dissip_path_named
  | law_cycle_open_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition dissip_conservation_law_count : nat := 4.

Lemma dissip_conservation_law_count_is_four :
  dissip_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive dissip_conservation_law_witness : Type :=
  | dissip_law_witness_open
  | dissip_law_witness_proved.

Definition evaluate_dissip_conservation_law_witness
  (law : dissip_conservation_law) (m : DissipConservationModality)
  : dissip_conservation_law_witness :=
  match m with
  | dissip_conservation_unwired
  | dissip_conservation_assumed
  | dissip_conservation_surrogate => dissip_law_witness_open
  | dissip_conservation_proved => dissip_law_witness_proved
  end.

Lemma all_dissip_conservation_laws_open_at_unwired :
  evaluate_dissip_conservation_law_witness law_dissip_path_named
    dissip_conservation_unwired = dissip_law_witness_open /\
  evaluate_dissip_conservation_law_witness law_cycle_open_refuse
    dissip_conservation_unwired = dissip_law_witness_open /\
  evaluate_dissip_conservation_law_witness law_green_invent_refuse
    dissip_conservation_unwired = dissip_law_witness_open /\
  evaluate_dissip_conservation_law_witness law_production_wired_refuse
    dissip_conservation_unwired = dissip_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  GRAPH-04 pins (structure witnesses — dissip laws not Proved)        *)
(* ------------------------------------------------------------------ *)

Definition graph04DissipProved : bool := false.

Lemma graph04_dissip_proved_false : graph04DissipProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_dissip_conservation_close
    dissip_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_dissip_conservation_close
    dissip_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  dissip_conservation_verdict_ok
    (evaluate_dissip_conservation_close
       dissip_conservation_unwired false false) =
  true.
Proof.
  unfold dissip_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named cyclic path close — reaction-cycle closed conserved         *)
(* ------------------------------------------------------------------ *)

Lemma dissip_cyclic_l1_named_ok :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent false false =
  verdict_path_named_ok.
Proof. reflexivity. Qed.

Theorem named_cyclic_dissip_conservation :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent false false =
  verdict_path_named_ok /\
  reactionCycleIdentityConserved reactionCycleFeCuClosed
    reactionCycleFeCuClosed = true /\
  reactionCycleClosed reactionCycleFeCuClosed = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma dissip_dissipative_l1_named_ok :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuDissipativeL1
    dissipClaimPathBarAbsent false false =
  verdict_path_named_ok.
Proof. reflexivity. Qed.

Theorem named_dissipative_path_conservation :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuDissipativeL1
    dissipClaimPathBarAbsent false false =
  verdict_path_named_ok /\
  bondPathDissipativeTyped bondPathFeCuDissipativeTyped = true.
Proof.
  split.
  - apply dissip_dissipative_l1_named_ok.
  - apply bond_path_fe_cu_dissipative_typed.
Qed.

Lemma dissip_named_close_ok :
  evaluate_dissip_conservation_close
    dissip_conservation_proved false false =
  verdict_path_named_ok.
Proof. reflexivity. Qed.

Theorem named_dissip_conservation_close :
  evaluate_dissip_conservation_close
    dissip_conservation_proved false false =
  verdict_path_named_ok /\
  dissip_conservation_authorized false false = true.
Proof.
  split.
  - apply dissip_named_close_ok.
  - unfold dissip_conservation_authorized.
    rewrite dissip_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial dissip fail-closed — dissip conservation refuse             *)
(* ------------------------------------------------------------------ *)

Lemma trivial_dissip_refused :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceTrivial
    dissipClaimPathBarAbsent false false =
  verdict_trivial_dissip_refuse.
Proof. reflexivity. Qed.

Theorem trivial_dissip_fail_closed :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceTrivial
    dissipClaimPathBarAbsent false false =
  verdict_trivial_dissip_refuse /\
  dissip_conservation_verdict_ok
    (evaluate_dissip_incidence
       dissip_conservation_unwired dissipIncidenceTrivial
       dissipClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_dissip_refused.
  - unfold dissip_conservation_verdict_ok.
    rewrite trivial_dissip_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cycle open fail-closed — reaction-cycle not closed refuse           *)
(* ------------------------------------------------------------------ *)

Lemma cycle_open_refused :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceCycleBroken
    dissipClaimPathBarAbsent false false =
  verdict_cycle_open_refuse.
Proof. reflexivity. Qed.

Theorem cycle_open_fail_closed :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceCycleBroken
    dissipClaimPathBarAbsent false false =
  verdict_cycle_open_refuse /\
  dissip_conservation_verdict_ok
    (evaluate_dissip_incidence
       dissip_conservation_unwired dissipIncidenceCycleBroken
       dissipClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply cycle_open_refused.
  - unfold dissip_conservation_verdict_ok.
    rewrite cycle_open_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Kind mismatch fail-closed — cycle ne dissipative refuse             *)
(* ------------------------------------------------------------------ *)

Lemma kind_mismatch_refused :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceKindMismatch
    dissipClaimPathBarAbsent false false =
  verdict_kind_mismatch_refuse.
Proof. reflexivity. Qed.

Theorem kind_mismatch_fail_closed :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceKindMismatch
    dissipClaimPathBarAbsent false false =
  verdict_kind_mismatch_refuse /\
  dissip_conservation_verdict_ok
    (evaluate_dissip_incidence
       dissip_conservation_unwired dissipIncidenceKindMismatch
       dissipClaimPathBarAbsent false false) =
  false.
Proof.
  split.
  - apply kind_mismatch_refused.
  - unfold dissip_conservation_verdict_ok.
    rewrite kind_mismatch_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_dissip_conservation_close
    dissip_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  dissip_conservation_verdict_ok
    (evaluate_dissip_conservation_close
       dissip_conservation_unwired true false) =
  false.
Proof.
  unfold dissip_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_dissip_incidence_refuse :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — dissip conservation refuse         *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  dissip_conservation_verdict_ok
    (evaluate_dissip_incidence
       dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
       dissipClaimPathBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold dissip_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuDissipativeL1
    dissipClaimPathBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — dissip lattice not production wired       *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_dissip_conservation_close
    dissip_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  dissip_conservation_verdict_ok
    (evaluate_dissip_conservation_close
       dissip_conservation_proved false true) =
  false.
Proof.
  unfold dissip_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Dissip conservation coherence scaffold — fixture witnesses          *)
(* ------------------------------------------------------------------ *)

Definition dissip_conservation_coherence_scaffold : bool :=
  dissip_conservation_verdict_beq
    (evaluate_dissip_conservation_close
       dissip_conservation_proved false false)
    verdict_path_named_ok &&
  dissip_conservation_verdict_beq
    (evaluate_dissip_conservation_close
       dissip_conservation_unwired true false)
    verdict_green_invent_refuse &&
  dissip_conservation_verdict_beq
    (evaluate_dissip_conservation_close
       dissip_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma dissip_conservation_coherence_scaffold_true :
  dissip_conservation_coherence_scaffold = true.
Proof.
  unfold dissip_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem dissip_conservation_coherence_scaffold_theorem :
  evaluate_dissip_conservation_close
    dissip_conservation_proved false false =
    verdict_path_named_ok /\
  evaluate_dissip_conservation_close
    dissip_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_dissip_conservation_close
    dissip_conservation_proved false true =
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
  | claim_dissip_conservation.

Definition dissip_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition dissip_conservation_knowing_fiber_ok : bool :=
  dissip_conservation_fiber_ok fiber_quantum_knowing.

Definition dissip_conservation_meso_acting_ok : bool :=
  dissip_conservation_fiber_ok fiber_meso_acting.

Lemma dissip_conservation_knowing_fiber_ok_true :
  dissip_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma dissip_conservation_meso_acting_not_ok :
  dissip_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem dissip_conservation_routes_knowing_not_meso :
  dissip_conservation_knowing_fiber_ok = true /\
  dissip_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply dissip_conservation_knowing_fiber_ok_true.
  - apply dissip_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  dissip_conservation_knowing_fiber_ok &&
  negb dissip_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, dissip_conservation_knowing_fiber_ok,
    dissip_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named dissip + fail-closed + fiber + GRAPH-04  *)
(* ------------------------------------------------------------------ *)

Theorem dissip_conservation_fixture_scaffold :
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuCyclicL1
    dissipClaimPathBarAbsent false false =
    verdict_path_named_ok /\
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceTrivial
    dissipClaimPathBarAbsent false false =
    verdict_trivial_dissip_refuse /\
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceCycleBroken
    dissipClaimPathBarAbsent false false =
    verdict_cycle_open_refuse /\
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceKindMismatch
    dissipClaimPathBarAbsent false false =
    verdict_kind_mismatch_refuse /\
  evaluate_dissip_incidence
    dissip_conservation_unwired dissipIncidenceFeCuDissipativeL1
    dissipClaimPathBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_dissip_conservation_close
    dissip_conservation_unwired false false =
    verdict_unwired_ok /\
  dissip_conservation_knowing_fiber_ok = true /\
  dissip_conservation_meso_acting_ok = false /\
  graph04DissipProved = false /\
  cycleNeDissipativePath = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — dissip conservation) *)
(* ------------------------------------------------------------------ *)

Definition reactionCycleAuthority : string :=
  "umst/umst-chem/src/reaction_cycle.rs".

Definition chemIntProveGraph04DissipAuthority : string :=
  "CHEM-INT-PROVE-GRAPH-04-DISSIP".

Definition dissipConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-DISSIP-CONSERVATION".

Definition dissipConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-DISSIP-CONSERVATION GRAPH-04 dissip conservation cyclic vs dissipative path identity conserved reaction-cycle closed bond-path dissipative typed cycle ne dissipative kind trivial dissip fail-closed GREEN invent fail-closed proved-without-bar fail-closed graph04DissipProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second dissip axiom not GREEN DFT not physics GREEN not production_wired".

Lemma dissip_conservation_cell_id :
  dissipConservationCellId = "CHEM-FORMAL-Q-COQ-DISSIP-CONSERVATION".
Proof. reflexivity. Qed.

Lemma dissip_conservation_cites_reaction_cycle_rs :
  reactionCycleAuthority <> "".
Proof. discriminate. Qed.

Lemma dissip_conservation_cites_int_prove_graph_04_dissip :
  chemIntProveGraph04DissipAuthority = "CHEM-INT-PROVE-GRAPH-04-DISSIP".
Proof. reflexivity. Qed.

Lemma dissip_conservation_cites_marker :
  dissipativePathMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second dissip   *)
(* ------------------------------------------------------------------ *)

Definition dissipSecondLawConservationFraming : string :=
  "second_law_conservation_dissip_one_axiom_not_second_dissip_axiom".

Lemma dissip_not_second_dissip_axiom :
  dissipSecondLawConservationFraming <> "second_dissip_axiom".
Proof. discriminate. Qed.

Lemma dissip_second_law_conservation_framing :
  dissipSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma dissip_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma dissip_conservation_modality_unwired :
  dissipConservationModalityCurrent = dissip_conservation_unwired.
Proof. reflexivity. Qed.

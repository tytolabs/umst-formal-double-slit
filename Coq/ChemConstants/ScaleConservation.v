(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ScaleConservation.v                                   *)
(*                                                                      *)
(*  Knowing-fiber Coq: SCALE-01 **commuting-square conservation**.     *)
(*  Q→meso, meso→macro, Q→macro direct legs named; composed indirect   *)
(*  path identity conserved vs direct (typed, Unwired). Missing-leg    *)
(*  fail-closed; GREEN invent fail-closed; Proved-without-bar            *)
(*  fail-closed. Geometry routes knowing/quantum fiber not meso acting.  *)
(*  Distinct from ScaleOccupancyZCommute.v (v24 Z-identity). Not 118²   *)
(*  GREEN table.                                                         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — **scale** commute is not a second axiom. *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  SCALE-01 **scale** **conservation** modality (Unwired / Assumed /   *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive ScaleConservationModality : Type :=
  | scale_conservation_unwired
  | scale_conservation_assumed
  | scale_conservation_proved
  | scale_conservation_surrogate.

Definition scaleConservationModalityCurrent : ScaleConservationModality :=
  scale_conservation_unwired.

Definition scale_lattice_cardinality : nat := 4.

Lemma scale_lattice_cardinality_is_four :
  scale_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma scale_lattice_not_118_squared :
  negb (Nat.eqb scale_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold scale_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — **scale** element **conservation** scaffold         *)
(*  (not 118² GREEN table)                                             *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition scale_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition scale_element_iron_z : nat := 26.
Definition scale_element_copper_z : nat := 29.
Definition scale_element_oganesson_z : nat := 118.

Lemma scale_iron_z_is_26 :
  scale_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma scale_copper_z_is_29 :
  scale_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma scale_oganesson_z_is_118 :
  scale_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma scale_fe_cu_z_valid :
  scale_element_z_valid scale_element_iron_z = true /\
  scale_element_z_valid scale_element_copper_z = true.
Proof.
  split; unfold scale_element_z_valid, scale_element_iron_z,
    scale_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma scale_oganesson_z_valid :
  scale_element_z_valid scale_element_oganesson_z = true.
Proof.
  unfold scale_element_z_valid, scale_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** levels — Q ↔ meso ↔ macro ladder (knowing fiber)          *)
(* ------------------------------------------------------------------ *)

Inductive scale_level : Type :=
  | scale_quantum
  | scale_meso
  | scale_macro.

Definition scale_level_beq (l1 l2 : scale_level) : bool :=
  match l1, l2 with
  | scale_quantum, scale_quantum => true
  | scale_meso, scale_meso => true
  | scale_macro, scale_macro => true
  | _, _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  **Scale** commuting legs — three legs of the square                  *)
(* ------------------------------------------------------------------ *)

Inductive scale_commuting_leg : Type :=
  | leg_quantum_to_meso
  | leg_meso_to_macro
  | leg_quantum_to_macro_direct.

Definition scale_leg_source (leg : scale_commuting_leg) : scale_level :=
  match leg with
  | leg_quantum_to_meso => scale_quantum
  | leg_meso_to_macro => scale_meso
  | leg_quantum_to_macro_direct => scale_quantum
  end.

Definition scale_leg_target (leg : scale_commuting_leg) : scale_level :=
  match leg with
  | leg_quantum_to_meso => scale_meso
  | leg_meso_to_macro => scale_macro
  | leg_quantum_to_macro_direct => scale_macro
  end.

Definition scaleLegQuantumToMeso : scale_commuting_leg := leg_quantum_to_meso.
Definition scaleLegMesoToMacro : scale_commuting_leg := leg_meso_to_macro.
Definition scaleLegQuantumToMacroDirect : scale_commuting_leg :=
  leg_quantum_to_macro_direct.

Lemma scale_leg_quantum_to_meso_named :
  scaleLegQuantumToMeso = leg_quantum_to_meso.
Proof. reflexivity. Qed.

Lemma scale_leg_meso_to_macro_named :
  scaleLegMesoToMacro = leg_meso_to_macro.
Proof. reflexivity. Qed.

Lemma scale_leg_quantum_to_macro_direct_named :
  scaleLegQuantumToMacroDirect = leg_quantum_to_macro_direct.
Proof. reflexivity. Qed.

Definition scale_leg_indirect_composes_bool : bool :=
  scale_level_beq
    (scale_leg_target scaleLegQuantumToMeso)
    (scale_leg_source scaleLegMesoToMacro).

Definition scale_leg_direct_endpoints_match_bool : bool :=
  scale_level_beq
    (scale_leg_source scaleLegQuantumToMeso)
    (scale_leg_source scaleLegQuantumToMacroDirect) &&
  scale_level_beq
    (scale_leg_target scaleLegMesoToMacro)
    (scale_leg_target scaleLegQuantumToMacroDirect).

Lemma scale_leg_indirect_composes_levels :
  scale_leg_target scaleLegQuantumToMeso = scale_leg_source scaleLegMesoToMacro.
Proof. reflexivity. Qed.

Lemma scale_leg_indirect_composes_bool_true :
  scale_leg_indirect_composes_bool = true.
Proof. reflexivity. Qed.

Lemma scale_leg_direct_endpoints_match :
  scale_leg_source scaleLegQuantumToMeso =
    scale_leg_source scaleLegQuantumToMacroDirect /\
  scale_leg_target scaleLegMesoToMacro =
    scale_leg_target scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

Lemma scale_leg_direct_endpoints_match_bool_true :
  scale_leg_direct_endpoints_match_bool = true.
Proof. reflexivity. Qed.

Lemma scale_leg_distinct_indirect_vs_direct :
  negb (scale_level_beq
    (scale_leg_source scaleLegQuantumToMeso)
    (scale_leg_target scaleLegQuantumToMeso)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** binding — parent Z identity across **scale** legs          *)
(* ------------------------------------------------------------------ *)

Record scale_binding : Type := {
  scale_parent_z : nat
}.

Definition scaleBindingFe : scale_binding :=
  {| scale_parent_z := scale_element_iron_z |}.

Definition scaleBindingCu : scale_binding :=
  {| scale_parent_z := scale_element_copper_z |}.

Definition scaleBindingOg : scale_binding :=
  {| scale_parent_z := scale_element_oganesson_z |}.

Definition scaleBindingTrivial : scale_binding :=
  {| scale_parent_z := 0 |}.

Definition scaleBindingNontrivial (b : scale_binding) : bool :=
  Nat.ltb 0 (scale_parent_z b).

Lemma scale_binding_fe_nontrivial :
  scaleBindingNontrivial scaleBindingFe = true.
Proof. reflexivity. Qed.

Lemma scale_binding_trivial_not_nontrivial :
  scaleBindingNontrivial scaleBindingTrivial = false.
Proof. reflexivity. Qed.

Definition scaleBindingIdentityConserved (b1 b2 : scale_binding) : bool :=
  Nat.eqb (scale_parent_z b1) (scale_parent_z b2).

Lemma scale_binding_fe_identity_conserved :
  scaleBindingIdentityConserved scaleBindingFe scaleBindingFe = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** leg lifts — typed identity placeholders (Unwired)         *)
(* ------------------------------------------------------------------ *)

Definition liftQuantumToMeso (z : nat) : nat := z.

Definition liftMesoToMacro (z : nat) : nat := z.

Definition liftQuantumToMacroDirect (z : nat) : nat := z.

Lemma lift_quantum_to_meso_identity (z : nat) :
  liftQuantumToMeso z = z.
Proof. reflexivity. Qed.

Lemma lift_meso_to_macro_identity (z : nat) :
  liftMesoToMacro z = z.
Proof. reflexivity. Qed.

Lemma lift_quantum_to_macro_direct_identity (z : nat) :
  liftQuantumToMacroDirect z = z.
Proof. reflexivity. Qed.

Definition scaleComposedIdentity (z : nat) : nat :=
  liftMesoToMacro (liftQuantumToMeso z).

Definition scaleDirectIdentity (z : nat) : nat :=
  liftQuantumToMacroDirect z.

Definition scaleComposedEqualsDirect (z : nat) : bool :=
  Nat.eqb (scaleComposedIdentity z) (scaleDirectIdentity z).

Lemma scale_composed_equals_direct_identity (z : nat) :
  scaleComposedEqualsDirect z = true.
Proof.
  unfold scaleComposedEqualsDirect, scaleComposedIdentity, scaleDirectIdentity,
    liftMesoToMacro, liftQuantumToMeso, liftQuantumToMacroDirect.
  apply Nat.eqb_refl.
Qed.

Theorem scale_commuting_square_identity_conserved :
  forall z : nat,
    scaleComposedIdentity z = scaleDirectIdentity z.
Proof.
  intros z.
  reflexivity.
Qed.

Lemma scale_fe_composed_equals_direct :
  scaleComposedEqualsDirect scale_element_iron_z = true.
Proof. apply scale_composed_equals_direct_identity. Qed.

Lemma scale_cu_composed_equals_direct :
  scaleComposedEqualsDirect scale_element_copper_z = true.
Proof. apply scale_composed_equals_direct_identity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** commute diagram — three legs named (scaffold)             *)
(* ------------------------------------------------------------------ *)

Record scale_commute_diagram : Type := {
  via_meso : scale_commuting_leg;
  then_macro : scale_commuting_leg;
  direct : scale_commuting_leg;
  has_quantum_to_meso : bool;
  has_meso_to_macro : bool;
  has_quantum_to_macro_direct : bool
}.

Definition scaleCommuteDiagramNamed : scale_commute_diagram :=
  {| via_meso := scaleLegQuantumToMeso;
     then_macro := scaleLegMesoToMacro;
     direct := scaleLegQuantumToMacroDirect;
     has_quantum_to_meso := true;
     has_meso_to_macro := true;
     has_quantum_to_macro_direct := true |}.

Definition scaleCommuteDiagramMissingDirect : scale_commute_diagram :=
  {| via_meso := scaleLegQuantumToMeso;
     then_macro := scaleLegMesoToMacro;
     direct := scaleLegQuantumToMacroDirect;
     has_quantum_to_meso := true;
     has_meso_to_macro := true;
     has_quantum_to_macro_direct := false |}.

Definition scaleCommuteDiagramMissingMesoLeg : scale_commute_diagram :=
  {| via_meso := scaleLegQuantumToMeso;
     then_macro := scaleLegMesoToMacro;
     direct := scaleLegQuantumToMacroDirect;
     has_quantum_to_meso := true;
     has_meso_to_macro := false;
     has_quantum_to_macro_direct := true |}.

Definition scaleCommuteDiagramTrivial : scale_commute_diagram :=
  {| via_meso := scaleLegQuantumToMeso;
     then_macro := scaleLegMesoToMacro;
     direct := scaleLegQuantumToMacroDirect;
     has_quantum_to_meso := false;
     has_meso_to_macro := false;
     has_quantum_to_macro_direct := false |}.

Definition scaleCommuteDiagramAllLegsPresent (d : scale_commute_diagram) : bool :=
  d.(has_quantum_to_meso) &&
  d.(has_meso_to_macro) &&
  d.(has_quantum_to_macro_direct).

Definition scaleCommuteDiagramLegsNamed (d : scale_commute_diagram) : bool :=
  scale_level_beq (scale_leg_source d.(via_meso)) scale_quantum &&
  scale_level_beq (scale_leg_target d.(via_meso)) scale_meso &&
  scale_level_beq (scale_leg_source d.(then_macro)) scale_meso &&
  scale_level_beq (scale_leg_target d.(then_macro)) scale_macro &&
  scale_level_beq (scale_leg_source d.(direct)) scale_quantum &&
  scale_level_beq (scale_leg_target d.(direct)) scale_macro.

Lemma scale_commute_diagram_named_all_legs :
  scaleCommuteDiagramAllLegsPresent scaleCommuteDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma scale_commute_diagram_named_legs_named :
  scaleCommuteDiagramLegsNamed scaleCommuteDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma scale_commute_diagram_missing_direct_not_all_legs :
  scaleCommuteDiagramAllLegsPresent scaleCommuteDiagramMissingDirect = false.
Proof. reflexivity. Qed.

Lemma scale_commute_diagram_missing_meso_not_all_legs :
  scaleCommuteDiagramAllLegsPresent scaleCommuteDiagramMissingMesoLeg = false.
Proof. reflexivity. Qed.

Lemma scale_commute_diagram_trivial_not_all_legs :
  scaleCommuteDiagramAllLegsPresent scaleCommuteDiagramTrivial = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** incidence — binding + diagram witness                     *)
(* ------------------------------------------------------------------ *)

Record scale_incidence : Type := {
  scale_inc_binding : scale_binding;
  scale_inc_diagram : scale_commute_diagram;
  scale_inc_level : nat
}.

Definition scaleIncidenceNontrivial (h : scale_incidence) : bool :=
  Nat.ltb 0 (scale_inc_level h).

Definition scaleIncidenceFeCuNamedL1 : scale_incidence :=
  {| scale_inc_binding := scaleBindingFe;
     scale_inc_diagram := scaleCommuteDiagramNamed;
     scale_inc_level := 1 |}.

Definition scaleIncidenceCuNamedL1 : scale_incidence :=
  {| scale_inc_binding := scaleBindingCu;
     scale_inc_diagram := scaleCommuteDiagramNamed;
     scale_inc_level := 1 |}.

Definition scaleIncidenceTrivial : scale_incidence :=
  {| scale_inc_binding := scaleBindingTrivial;
     scale_inc_diagram := scaleCommuteDiagramTrivial;
     scale_inc_level := 0 |}.

Definition scaleIncidenceMissingDirectLeg : scale_incidence :=
  {| scale_inc_binding := scaleBindingFe;
     scale_inc_diagram := scaleCommuteDiagramMissingDirect;
     scale_inc_level := 1 |}.

Definition scaleIncidenceMissingMesoLeg : scale_incidence :=
  {| scale_inc_binding := scaleBindingFe;
     scale_inc_diagram := scaleCommuteDiagramMissingMesoLeg;
     scale_inc_level := 1 |}.

Lemma scale_incidence_fe_cu_nontrivial :
  scaleIncidenceNontrivial scaleIncidenceFeCuNamedL1 = true.
Proof. reflexivity. Qed.

Lemma scale_incidence_trivial_not_nontrivial :
  scaleIncidenceNontrivial scaleIncidenceTrivial = false.
Proof. reflexivity. Qed.

Lemma scale_incidence_fe_cu_composed_direct :
  scaleComposedEqualsDirect (scale_parent_z (scale_inc_binding scaleIncidenceFeCuNamedL1)) = true.
Proof. apply scale_composed_equals_direct_identity. Qed.

(* ------------------------------------------------------------------ *)
(*  Indirect vs direct markers — **scale** legs not interchangeable      *)
(* ------------------------------------------------------------------ *)

Definition indirectPathMarker : string := "chem_l0_scale_quantum_to_meso_v1".
Definition directPathMarker : string := "chem_l0_scale_quantum_to_macro_direct_v1".

Lemma indirect_ne_direct_marker :
  indirectPathMarker <> directPathMarker.
Proof. discriminate. Qed.

Definition indirectNeDirectPath : bool :=
  scale_leg_indirect_composes_bool &&
  scale_leg_direct_endpoints_match_bool &&
  scaleComposedEqualsDirect scale_element_iron_z &&
  scaleCommuteDiagramAllLegsPresent scaleCommuteDiagramNamed.

Lemma indirect_ne_direct_path_true : indirectNeDirectPath = true.
Proof.
  unfold indirectNeDirectPath.
  rewrite scale_leg_indirect_composes_bool_true.
  rewrite scale_leg_direct_endpoints_match_bool_true.
  rewrite scale_fe_composed_equals_direct.
  simpl.
  reflexivity.
Qed.

Theorem indirect_ne_direct_path_identity :
  indirectNeDirectPath = true /\
  indirectPathMarker <> directPathMarker.
Proof.
  split.
  - apply indirect_ne_direct_path_true.
  - apply indirect_ne_direct_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** bar — Proved-without-bar fail-closed                       *)
(* ------------------------------------------------------------------ *)

Inductive scale_commute_bar_presence : Type :=
  | scale_bar_absent
  | scale_bar_present.

Record scale_claim_commute_bar : Type := {
  scale_bar_presence : scale_commute_bar_presence;
  scale_bar_defect_total : nat
}.

Definition scaleClaimCommuteBarAbsent : scale_claim_commute_bar :=
  {| scale_bar_presence := scale_bar_absent; scale_bar_defect_total := 0 |}.

Definition scaleClaimCommuteBarZeroDefect : scale_claim_commute_bar :=
  {| scale_bar_presence := scale_bar_present; scale_bar_defect_total := 0 |}.

Definition scale_claim_commute_bar_zero_defect (b : scale_claim_commute_bar) : bool :=
  match scale_bar_presence b with
  | scale_bar_absent => false
  | scale_bar_present => Nat.eqb (scale_bar_defect_total b) 0
  end.

Lemma scale_claim_commute_bar_zero_defect_true :
  scale_claim_commute_bar_zero_defect scaleClaimCommuteBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma scale_claim_commute_bar_absent_not_zero_defect :
  scale_claim_commute_bar_zero_defect scaleClaimCommuteBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** **conservation** verdict — fail-closed close lattice       *)
(* ------------------------------------------------------------------ *)

Inductive scale_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_scale_named_ok
  | verdict_trivial_scale_refuse
  | verdict_missing_leg_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition scale_conservation_verdict_ok
  (v : scale_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_scale_named_ok => true
  | _ => false
  end.

Definition scale_conservation_verdict_beq
  (v1 v2 : scale_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_scale_named_ok, verdict_scale_named_ok => true
  | verdict_trivial_scale_refuse, verdict_trivial_scale_refuse => true
  | verdict_missing_leg_refuse, verdict_missing_leg_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_scale_incidence
  (m : ScaleConservationModality)
  (h : scale_incidence)
  (b : scale_claim_commute_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : scale_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (scaleIncidenceNontrivial h)
            then verdict_trivial_scale_refuse
            else if negb (scaleCommuteDiagramAllLegsPresent (scale_inc_diagram h))
                 then verdict_missing_leg_refuse
                 else
                   match m with
                   | scale_conservation_unwired => verdict_scale_named_ok
                   | scale_conservation_assumed
                   | scale_conservation_surrogate => verdict_unwired_ok
                   | scale_conservation_proved => verdict_proved_without_bar_refuse
                   end.

Definition evaluate_scale_conservation_close
  (m : ScaleConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : scale_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | scale_conservation_unwired => verdict_unwired_ok
    | scale_conservation_assumed
    | scale_conservation_proved
    | scale_conservation_surrogate => verdict_scale_named_ok
    end.

Definition scale_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_scale_conservation_close
          scale_conservation_proved claim_physics_green claim_production_wired with
  | verdict_scale_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  **Scale** **conservation** law cells — four laws, open @ Unwired     *)
(* ------------------------------------------------------------------ *)

Inductive scale_conservation_law : Type :=
  | law_scale_commute_named
  | law_missing_leg_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition scale_conservation_law_count : nat := 4.

Lemma scale_conservation_law_count_is_four :
  scale_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive scale_conservation_law_witness : Type :=
  | scale_law_witness_open
  | scale_law_witness_proved.

Definition evaluate_scale_conservation_law_witness
  (law : scale_conservation_law) (m : ScaleConservationModality)
  : scale_conservation_law_witness :=
  match m with
  | scale_conservation_unwired
  | scale_conservation_assumed
  | scale_conservation_surrogate => scale_law_witness_open
  | scale_conservation_proved => scale_law_witness_proved
  end.

Lemma all_scale_conservation_laws_open_at_unwired :
  evaluate_scale_conservation_law_witness law_scale_commute_named
    scale_conservation_unwired = scale_law_witness_open /\
  evaluate_scale_conservation_law_witness law_missing_leg_refuse
    scale_conservation_unwired = scale_law_witness_open /\
  evaluate_scale_conservation_law_witness law_green_invent_refuse
    scale_conservation_unwired = scale_law_witness_open /\
  evaluate_scale_conservation_law_witness law_production_wired_refuse
    scale_conservation_unwired = scale_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SCALE-01 pins (structure witnesses — **scale** laws not Proved)    *)
(* ------------------------------------------------------------------ *)

Definition scale01CommuteProved : bool := false.

Lemma scale01_commute_proved_false : scale01CommuteProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_scale_conservation_close
    scale_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_scale_conservation_close
    scale_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  scale_conservation_verdict_ok
    (evaluate_scale_conservation_close
       scale_conservation_unwired false false) =
  true.
Proof.
  unfold scale_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe **scale** close — composed = direct identity conserved     *)
(* ------------------------------------------------------------------ *)

Lemma scale_fe_cu_named_ok :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false false =
  verdict_scale_named_ok.
Proof. reflexivity. Qed.

Theorem named_scale_commuting_square_conservation :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false false =
  verdict_scale_named_ok /\
  scaleComposedEqualsDirect (scale_parent_z (scale_inc_binding scaleIncidenceFeCuNamedL1)) = true /\
  scaleBindingIdentityConserved (scale_inc_binding scaleIncidenceFeCuNamedL1)
    (scale_inc_binding scaleIncidenceFeCuNamedL1) = true /\
  scaleCommuteDiagramAllLegsPresent (scale_inc_diagram scaleIncidenceFeCuNamedL1) = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma scale_cu_named_ok :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceCuNamedL1
    scaleClaimCommuteBarAbsent false false =
  verdict_scale_named_ok.
Proof. reflexivity. Qed.

Theorem named_cu_scale_commuting_square_conservation :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceCuNamedL1
    scaleClaimCommuteBarAbsent false false =
  verdict_scale_named_ok /\
  scaleComposedEqualsDirect (scale_parent_z (scale_inc_binding scaleIncidenceCuNamedL1)) = true.
Proof.
  split.
  - apply scale_cu_named_ok.
  - apply scale_cu_composed_equals_direct.
Qed.

Lemma scale_named_close_ok :
  evaluate_scale_conservation_close
    scale_conservation_proved false false =
  verdict_scale_named_ok.
Proof. reflexivity. Qed.

Theorem named_scale_conservation_close :
  evaluate_scale_conservation_close
    scale_conservation_proved false false =
  verdict_scale_named_ok /\
  scale_conservation_authorized false false = true.
Proof.
  split.
  - apply scale_named_close_ok.
  - unfold scale_conservation_authorized.
    rewrite scale_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial **scale** fail-closed — **conservation** refuse             *)
(* ------------------------------------------------------------------ *)

Lemma trivial_scale_refused :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceTrivial
    scaleClaimCommuteBarAbsent false false =
  verdict_trivial_scale_refuse.
Proof. reflexivity. Qed.

Theorem trivial_scale_fail_closed :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceTrivial
    scaleClaimCommuteBarAbsent false false =
  verdict_trivial_scale_refuse /\
  scale_conservation_verdict_ok
    (evaluate_scale_incidence
       scale_conservation_unwired scaleIncidenceTrivial
       scaleClaimCommuteBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_scale_refused.
  - unfold scale_conservation_verdict_ok.
    rewrite trivial_scale_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Missing-leg fail-closed — **scale** commute square refuse           *)
(* ------------------------------------------------------------------ *)

Lemma missing_direct_leg_refused :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingDirectLeg
    scaleClaimCommuteBarAbsent false false =
  verdict_missing_leg_refuse.
Proof. reflexivity. Qed.

Theorem missing_direct_leg_fail_closed :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingDirectLeg
    scaleClaimCommuteBarAbsent false false =
  verdict_missing_leg_refuse /\
  scale_conservation_verdict_ok
    (evaluate_scale_incidence
       scale_conservation_unwired scaleIncidenceMissingDirectLeg
       scaleClaimCommuteBarAbsent false false) =
  false.
Proof.
  split.
  - apply missing_direct_leg_refused.
  - unfold scale_conservation_verdict_ok.
    rewrite missing_direct_leg_refused.
    reflexivity.
Qed.

Lemma missing_meso_leg_refused :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingMesoLeg
    scaleClaimCommuteBarAbsent false false =
  verdict_missing_leg_refuse.
Proof. reflexivity. Qed.

Theorem missing_meso_leg_fail_closed :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingMesoLeg
    scaleClaimCommuteBarAbsent false false =
  verdict_missing_leg_refuse /\
  scale_conservation_verdict_ok
    (evaluate_scale_incidence
       scale_conservation_unwired scaleIncidenceMissingMesoLeg
       scaleClaimCommuteBarAbsent false false) =
  false.
Proof.
  split.
  - apply missing_meso_leg_refused.
  - unfold scale_conservation_verdict_ok.
    rewrite missing_meso_leg_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_scale_conservation_close
    scale_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  scale_conservation_verdict_ok
    (evaluate_scale_conservation_close
       scale_conservation_unwired true false) =
  false.
Proof.
  unfold scale_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_scale_incidence_refuse :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — **scale** **conservation** refuse  *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  scale_conservation_verdict_ok
    (evaluate_scale_incidence
       scale_conservation_unwired scaleIncidenceFeCuNamedL1
       scaleClaimCommuteBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold scale_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceCuNamedL1
    scaleClaimCommuteBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — **scale** lattice not production wired      *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_scale_conservation_close
    scale_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  scale_conservation_verdict_ok
    (evaluate_scale_conservation_close
       scale_conservation_proved false true) =
  false.
Proof.
  unfold scale_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Scale** **conservation** coherence scaffold — fixture witnesses    *)
(* ------------------------------------------------------------------ *)

Definition scale_conservation_coherence_scaffold : bool :=
  scale_conservation_verdict_beq
    (evaluate_scale_conservation_close
       scale_conservation_proved false false)
    verdict_scale_named_ok &&
  scale_conservation_verdict_beq
    (evaluate_scale_conservation_close
       scale_conservation_unwired true false)
    verdict_green_invent_refuse &&
  scale_conservation_verdict_beq
    (evaluate_scale_conservation_close
       scale_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma scale_conservation_coherence_scaffold_true :
  scale_conservation_coherence_scaffold = true.
Proof.
  unfold scale_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem scale_conservation_coherence_scaffold_theorem :
  evaluate_scale_conservation_close
    scale_conservation_proved false false =
    verdict_scale_named_ok /\
  evaluate_scale_conservation_close
    scale_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_scale_conservation_close
    scale_conservation_proved false true =
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
  | claim_scale_conservation.

Definition scale_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition scale_conservation_knowing_fiber_ok : bool :=
  scale_conservation_fiber_ok fiber_quantum_knowing.

Definition scale_conservation_meso_acting_ok : bool :=
  scale_conservation_fiber_ok fiber_meso_acting.

Lemma scale_conservation_knowing_fiber_ok_true :
  scale_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma scale_conservation_meso_acting_not_ok :
  scale_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem scale_conservation_routes_knowing_not_meso :
  scale_conservation_knowing_fiber_ok = true /\
  scale_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply scale_conservation_knowing_fiber_ok_true.
  - apply scale_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  scale_conservation_knowing_fiber_ok &&
  negb scale_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, scale_conservation_knowing_fiber_ok,
    scale_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named **scale** + fail-closed + fiber + SCALE-01 *)
(* ------------------------------------------------------------------ *)

Theorem scale_conservation_fixture_scaffold :
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false false =
    verdict_scale_named_ok /\
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceTrivial
    scaleClaimCommuteBarAbsent false false =
    verdict_trivial_scale_refuse /\
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingDirectLeg
    scaleClaimCommuteBarAbsent false false =
    verdict_missing_leg_refuse /\
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceMissingMesoLeg
    scaleClaimCommuteBarAbsent false false =
    verdict_missing_leg_refuse /\
  evaluate_scale_incidence
    scale_conservation_unwired scaleIncidenceFeCuNamedL1
    scaleClaimCommuteBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_scale_conservation_close
    scale_conservation_unwired false false =
    verdict_unwired_ok /\
  scale_conservation_knowing_fiber_ok = true /\
  scale_conservation_meso_acting_ok = false /\
  scale01CommuteProved = false /\
  indirectNeDirectPath = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — **scale** commute)  *)
(* ------------------------------------------------------------------ *)

Definition scaleCommutingDiagramsAuthority : string :=
  "umst/umst-chem/src/scale_commuting_diagrams.rs".

Definition chemL0Scale01Authority : string :=
  "CHEM-L0-SCALE-01".

Definition chemIntCrossScaleCommuteAuthority : string :=
  "CHEM-INT-CROSS-SCALE-COMMUTE".

Definition scaleConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-SCALE-CONSERVATION".

Definition scaleConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-SCALE-CONSERVATION SCALE-01 commuting-square conservation Q to meso meso to macro Q to macro direct composed equals direct identity conserved typed Unwired three legs named missing-leg fail-closed GREEN invent fail-closed proved-without-bar fail-closed scale01CommuteProved false Unwired geometry knowing quantum fiber not meso acting distinct from ScaleOccupancyZCommute one axiom second law conservation not second scale axiom not GREEN DFT not physics GREEN not production_wired".

Lemma scale_conservation_cell_id :
  scaleConservationCellId = "CHEM-FORMAL-Q-COQ-SCALE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma scale_conservation_cites_scale_commuting_diagrams_rs :
  scaleCommutingDiagramsAuthority <> "".
Proof. discriminate. Qed.

Lemma scale_conservation_cites_l0_scale_01 :
  chemL0Scale01Authority = "CHEM-L0-SCALE-01".
Proof. reflexivity. Qed.

Lemma scale_conservation_cites_int_cross_scale_commute :
  chemIntCrossScaleCommuteAuthority = "CHEM-INT-CROSS-SCALE-COMMUTE".
Proof. reflexivity. Qed.

Lemma scale_conservation_cites_marker :
  indirectPathMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not second scale  *)
(* ------------------------------------------------------------------ *)

Definition scaleSecondLawConservationFraming : string :=
  "second_law_conservation_scale_one_axiom_not_second_scale_axiom".

Lemma scale_not_second_scale_axiom :
  scaleSecondLawConservationFraming <> "second_scale_axiom".
Proof. discriminate. Qed.

Lemma scale_second_law_conservation_framing :
  scaleSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma scale_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma scale_conservation_modality_unwired :
  scaleConservationModalityCurrent = scale_conservation_unwired.
Proof. reflexivity. Qed.

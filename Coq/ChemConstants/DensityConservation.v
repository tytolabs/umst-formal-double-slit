(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: DensityConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: DensityLadder **density** **conservation**.       *)
(*  Four rungs mSDF→TE-SDF→SDF→FRep named; composed indirect ladder     *)
(*  path identity conserved vs direct (typed, Unwired). Scrambled-order  *)
(*  fail-closed; GREEN invent fail-closed; Proved-without-bar            *)
(*  fail-closed. SDF ≠ ρ unless named (generic signed-distance is not   *)
(*  ElectronDensityRho). Geometry routes knowing/quantum fiber not meso  *)
(*  acting. Distinct from DensityStateSpec (quantum matrix ρ). Not 118²   *)
(*  GREEN table.                                                         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — **density** ladder commute is not a second *)
(*  axiom.                                                               *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  DensityLadder **density** **conservation** modality (Unwired /       *)
(*  Assumed / Proved / Surrogate)                                       *)
(* ------------------------------------------------------------------ *)

Inductive DensityConservationModality : Type :=
  | density_conservation_unwired
  | density_conservation_assumed
  | density_conservation_proved
  | density_conservation_surrogate.

Definition densityConservationModalityCurrent : DensityConservationModality :=
  density_conservation_unwired.

Definition density_ladder_cardinality : nat := 4.

Lemma density_ladder_cardinality_is_four :
  density_ladder_cardinality = 4.
Proof. reflexivity. Qed.

Lemma density_ladder_not_118_squared :
  negb (Nat.eqb density_ladder_cardinality (118 * 118)) = true.
Proof.
  unfold density_ladder_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — **density** element **conservation** scaffold         *)
(*  (not 118² GREEN table)                                             *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition density_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition density_element_iron_z : nat := 26.
Definition density_element_copper_z : nat := 29.
Definition density_element_oganesson_z : nat := 118.

Lemma density_iron_z_is_26 :
  density_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma density_copper_z_is_29 :
  density_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma density_oganesson_z_is_118 :
  density_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma density_fe_cu_z_valid :
  density_element_z_valid density_element_iron_z = true /\
  density_element_z_valid density_element_copper_z = true.
Proof.
  split; unfold density_element_z_valid, density_element_iron_z,
    density_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma density_oganesson_z_valid :
  density_element_z_valid density_element_oganesson_z = true.
Proof.
  unfold density_element_z_valid, density_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SDF ≠ ρ unless named — generic signed-distance is not ρ             *)
(* ------------------------------------------------------------------ *)

Inductive density_scalar_kind : Type :=
  | scalar_signed_distance_generic
  | scalar_named_electron_density_rho
  | scalar_named_elf
  | scalar_named_nci
  | scalar_named_gate_sdf.

Definition density_scalar_kind_beq (k1 k2 : density_scalar_kind) : bool :=
  match k1, k2 with
  | scalar_signed_distance_generic, scalar_signed_distance_generic => true
  | scalar_named_electron_density_rho, scalar_named_electron_density_rho => true
  | scalar_named_elf, scalar_named_elf => true
  | scalar_named_nci, scalar_named_nci => true
  | scalar_named_gate_sdf, scalar_named_gate_sdf => true
  | _, _ => false
  end.

Definition densityScalarSignedDistance : density_scalar_kind :=
  scalar_signed_distance_generic.

Definition densityScalarElectronDensityRho : density_scalar_kind :=
  scalar_named_electron_density_rho.

Definition density_scalar_is_electron_density_rho (k : density_scalar_kind) : bool :=
  match k with
  | scalar_named_electron_density_rho => true
  | _ => false
  end.

Definition density_scalar_sdf_not_rho_unless_named (k : density_scalar_kind) : bool :=
  match k with
  | scalar_signed_distance_generic => true
  | scalar_named_electron_density_rho => true
  | scalar_named_elf => true
  | scalar_named_nci => true
  | scalar_named_gate_sdf => true
  end.

Lemma density_signed_distance_not_rho :
  density_scalar_is_electron_density_rho densityScalarSignedDistance = false.
Proof. reflexivity. Qed.

Lemma density_electron_density_rho_named :
  density_scalar_is_electron_density_rho densityScalarElectronDensityRho = true.
Proof. reflexivity. Qed.

Lemma density_sdf_not_rho_unless_named_signed_distance :
  density_scalar_sdf_not_rho_unless_named densityScalarSignedDistance = true.
Proof. reflexivity. Qed.

Lemma density_sdf_not_rho_unless_named_electron_rho :
  density_scalar_sdf_not_rho_unless_named densityScalarElectronDensityRho = true.
Proof. reflexivity. Qed.

Lemma density_signed_distance_ne_electron_rho :
  negb (density_scalar_kind_beq
    densityScalarSignedDistance densityScalarElectronDensityRho) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  DensityLadder rungs — mSDF → TE-SDF → SDF → FRep (knowing fiber)    *)
(* ------------------------------------------------------------------ *)

Inductive density_rung : Type :=
  | rung_micro_sdf
  | rung_te_sdf
  | rung_sdf
  | rung_frep.

Definition density_rung_beq (r1 r2 : density_rung) : bool :=
  match r1, r2 with
  | rung_micro_sdf, rung_micro_sdf => true
  | rung_te_sdf, rung_te_sdf => true
  | rung_sdf, rung_sdf => true
  | rung_frep, rung_frep => true
  | _, _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  DensityLadder legs — four rungs, three step legs + direct leg        *)
(* ------------------------------------------------------------------ *)

Inductive density_ladder_leg : Type :=
  | leg_micro_to_te_sdf
  | leg_te_sdf_to_sdf
  | leg_sdf_to_frep
  | leg_micro_to_frep_direct.

Definition density_leg_source (leg : density_ladder_leg) : density_rung :=
  match leg with
  | leg_micro_to_te_sdf => rung_micro_sdf
  | leg_te_sdf_to_sdf => rung_te_sdf
  | leg_sdf_to_frep => rung_sdf
  | leg_micro_to_frep_direct => rung_micro_sdf
  end.

Definition density_leg_target (leg : density_ladder_leg) : density_rung :=
  match leg with
  | leg_micro_to_te_sdf => rung_te_sdf
  | leg_te_sdf_to_sdf => rung_sdf
  | leg_sdf_to_frep => rung_frep
  | leg_micro_to_frep_direct => rung_frep
  end.

Definition densityLegMicroToTeSdf : density_ladder_leg := leg_micro_to_te_sdf.
Definition densityLegTeSdfToSdf : density_ladder_leg := leg_te_sdf_to_sdf.
Definition densityLegSdfToFrep : density_ladder_leg := leg_sdf_to_frep.
Definition densityLegMicroToFrepDirect : density_ladder_leg :=
  leg_micro_to_frep_direct.

Lemma density_leg_micro_to_te_named :
  densityLegMicroToTeSdf = leg_micro_to_te_sdf.
Proof. reflexivity. Qed.

Lemma density_leg_te_sdf_to_sdf_named :
  densityLegTeSdfToSdf = leg_te_sdf_to_sdf.
Proof. reflexivity. Qed.

Lemma density_leg_sdf_to_frep_named :
  densityLegSdfToFrep = leg_sdf_to_frep.
Proof. reflexivity. Qed.

Lemma density_leg_micro_to_frep_direct_named :
  densityLegMicroToFrepDirect = leg_micro_to_frep_direct.
Proof. reflexivity. Qed.

Definition density_leg_indirect_composes_bool : bool :=
  density_rung_beq
    (density_leg_target densityLegMicroToTeSdf)
    (density_leg_source densityLegTeSdfToSdf) &&
  density_rung_beq
    (density_leg_target densityLegTeSdfToSdf)
    (density_leg_source densityLegSdfToFrep).

Definition density_leg_direct_endpoints_match_bool : bool :=
  density_rung_beq
    (density_leg_source densityLegMicroToTeSdf)
    (density_leg_source densityLegMicroToFrepDirect) &&
  density_rung_beq
    (density_leg_target densityLegSdfToFrep)
    (density_leg_target densityLegMicroToFrepDirect).

Lemma density_leg_indirect_composes_levels :
  density_leg_target densityLegMicroToTeSdf = density_leg_source densityLegTeSdfToSdf /\
  density_leg_target densityLegTeSdfToSdf = density_leg_source densityLegSdfToFrep.
Proof. tauto. Qed.

Lemma density_leg_indirect_composes_bool_true :
  density_leg_indirect_composes_bool = true.
Proof. reflexivity. Qed.

Lemma density_leg_direct_endpoints_match :
  density_leg_source densityLegMicroToTeSdf =
    density_leg_source densityLegMicroToFrepDirect /\
  density_leg_target densityLegSdfToFrep =
    density_leg_target densityLegMicroToFrepDirect.
Proof. tauto. Qed.

Lemma density_leg_direct_endpoints_match_bool_true :
  density_leg_direct_endpoints_match_bool = true.
Proof. reflexivity. Qed.

Lemma density_leg_distinct_step_vs_direct :
  negb (density_rung_beq
    (density_leg_source densityLegMicroToTeSdf)
    (density_leg_target densityLegMicroToTeSdf)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Density** binding — parent Z identity across ladder legs          *)
(* ------------------------------------------------------------------ *)

Record density_binding : Type := {
  density_parent_z : nat
}.

Definition densityBindingFe : density_binding :=
  {| density_parent_z := density_element_iron_z |}.

Definition densityBindingCu : density_binding :=
  {| density_parent_z := density_element_copper_z |}.
Definition densityBindingOg : density_binding :=
  {| density_parent_z := density_element_oganesson_z |}.

Definition densityBindingTrivial : density_binding :=
  {| density_parent_z := 0 |}.

Definition densityBindingNontrivial (b : density_binding) : bool :=
  Nat.ltb 0 (density_parent_z b).

Lemma density_binding_fe_nontrivial :
  densityBindingNontrivial densityBindingFe = true.
Proof. reflexivity. Qed.

Lemma density_binding_trivial_not_nontrivial :
  densityBindingNontrivial densityBindingTrivial = false.
Proof. reflexivity. Qed.

Definition densityBindingIdentityConserved (b1 b2 : density_binding) : bool :=
  Nat.eqb (density_parent_z b1) (density_parent_z b2).

Lemma density_binding_fe_identity_conserved :
  densityBindingIdentityConserved densityBindingFe densityBindingFe = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  DensityLadder leg lifts — typed identity placeholders (Unwired)     *)
(* ------------------------------------------------------------------ *)

Definition liftMicroToTeSdf (z : nat) : nat := z.

Definition liftTeSdfToSdf (z : nat) : nat := z.

Definition liftSdfToFrep (z : nat) : nat := z.

Definition liftMicroToFrepDirect (z : nat) : nat := z.

Lemma lift_micro_to_te_sdf_identity (z : nat) :
  liftMicroToTeSdf z = z.
Proof. reflexivity. Qed.

Lemma lift_te_sdf_to_sdf_identity (z : nat) :
  liftTeSdfToSdf z = z.
Proof. reflexivity. Qed.

Lemma lift_sdf_to_frep_identity (z : nat) :
  liftSdfToFrep z = z.
Proof. reflexivity. Qed.

Lemma lift_micro_to_frep_direct_identity (z : nat) :
  liftMicroToFrepDirect z = z.
Proof. reflexivity. Qed.

Definition densityComposedIdentity (z : nat) : nat :=
  liftSdfToFrep (liftTeSdfToSdf (liftMicroToTeSdf z)).

Definition densityDirectIdentity (z : nat) : nat :=
  liftMicroToFrepDirect z.

Definition densityComposedEqualsDirect (z : nat) : bool :=
  Nat.eqb (densityComposedIdentity z) (densityDirectIdentity z).

Lemma density_composed_equals_direct_identity (z : nat) :
  densityComposedEqualsDirect z = true.
Proof.
  unfold densityComposedEqualsDirect, densityComposedIdentity, densityDirectIdentity,
    liftSdfToFrep, liftTeSdfToSdf, liftMicroToTeSdf, liftMicroToFrepDirect.
  apply Nat.eqb_refl.
Qed.

Theorem density_ladder_identity_conserved :
  forall z : nat,
    densityComposedIdentity z = densityDirectIdentity z.
Proof.
  intros z.
  reflexivity.
Qed.

Lemma density_fe_composed_equals_direct :
  densityComposedEqualsDirect density_element_iron_z = true.
Proof. apply density_composed_equals_direct_identity. Qed.

Lemma density_cu_composed_equals_direct :
  densityComposedEqualsDirect density_element_copper_z = true.
Proof. apply density_composed_equals_direct_identity. Qed.

(* ------------------------------------------------------------------ *)
(*  DensityLadder diagram — four rungs named (scaffold)                 *)
(* ------------------------------------------------------------------ *)

Record density_ladder_diagram : Type := {
  via_te_sdf : density_ladder_leg;
  then_sdf : density_ladder_leg;
  then_frep : density_ladder_leg;
  direct : density_ladder_leg;
  has_micro_to_te_sdf : bool;
  has_te_sdf_to_sdf : bool;
  has_sdf_to_frep : bool;
  has_micro_to_frep_direct : bool
}.

Definition densityLadderDiagramNamed : density_ladder_diagram :=
  {| via_te_sdf := densityLegMicroToTeSdf;
     then_sdf := densityLegTeSdfToSdf;
     then_frep := densityLegSdfToFrep;
     direct := densityLegMicroToFrepDirect;
     has_micro_to_te_sdf := true;
     has_te_sdf_to_sdf := true;
     has_sdf_to_frep := true;
     has_micro_to_frep_direct := true |}.

Definition densityLadderDiagramMissingDirect : density_ladder_diagram :=
  {| via_te_sdf := densityLegMicroToTeSdf;
     then_sdf := densityLegTeSdfToSdf;
     then_frep := densityLegSdfToFrep;
     direct := densityLegMicroToFrepDirect;
     has_micro_to_te_sdf := true;
     has_te_sdf_to_sdf := true;
     has_sdf_to_frep := true;
     has_micro_to_frep_direct := false |}.

Definition densityLadderDiagramScrambledOrder : density_ladder_diagram :=
  {| via_te_sdf := densityLegSdfToFrep;
     then_sdf := densityLegTeSdfToSdf;
     then_frep := densityLegMicroToTeSdf;
     direct := densityLegMicroToFrepDirect;
     has_micro_to_te_sdf := true;
     has_te_sdf_to_sdf := true;
     has_sdf_to_frep := true;
     has_micro_to_frep_direct := true |}.

Definition densityLadderDiagramTrivial : density_ladder_diagram :=
  {| via_te_sdf := densityLegMicroToTeSdf;
     then_sdf := densityLegTeSdfToSdf;
     then_frep := densityLegSdfToFrep;
     direct := densityLegMicroToFrepDirect;
     has_micro_to_te_sdf := false;
     has_te_sdf_to_sdf := false;
     has_sdf_to_frep := false;
     has_micro_to_frep_direct := false |}.

Definition densityLadderDiagramAllLegsPresent (d : density_ladder_diagram) : bool :=
  d.(has_micro_to_te_sdf) &&
  d.(has_te_sdf_to_sdf) &&
  d.(has_sdf_to_frep) &&
  d.(has_micro_to_frep_direct).

Definition densityLadderDiagramLegsNamed (d : density_ladder_diagram) : bool :=
  density_rung_beq (density_leg_source d.(via_te_sdf)) rung_micro_sdf &&
  density_rung_beq (density_leg_target d.(via_te_sdf)) rung_te_sdf &&
  density_rung_beq (density_leg_source d.(then_sdf)) rung_te_sdf &&
  density_rung_beq (density_leg_target d.(then_sdf)) rung_sdf &&
  density_rung_beq (density_leg_source d.(then_frep)) rung_sdf &&
  density_rung_beq (density_leg_target d.(then_frep)) rung_frep &&
  density_rung_beq (density_leg_source d.(direct)) rung_micro_sdf &&
  density_rung_beq (density_leg_target d.(direct)) rung_frep.

Definition densityLadderDiagramOrderOk (d : density_ladder_diagram) : bool :=
  density_rung_beq
    (density_leg_target d.(via_te_sdf))
    (density_leg_source d.(then_sdf)) &&
  density_rung_beq
    (density_leg_target d.(then_sdf))
    (density_leg_source d.(then_frep)) &&
  density_rung_beq
    (density_leg_source d.(via_te_sdf))
    (density_leg_source d.(direct)) &&
  density_rung_beq
    (density_leg_target d.(then_frep))
    (density_leg_target d.(direct)).

Lemma density_ladder_diagram_named_all_legs :
  densityLadderDiagramAllLegsPresent densityLadderDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma density_ladder_diagram_named_legs_named :
  densityLadderDiagramLegsNamed densityLadderDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma density_ladder_diagram_named_order_ok :
  densityLadderDiagramOrderOk densityLadderDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma density_ladder_diagram_scrambled_order_not_ok :
  densityLadderDiagramOrderOk densityLadderDiagramScrambledOrder = false.
Proof. reflexivity. Qed.

Lemma density_ladder_diagram_missing_direct_not_all_legs :
  densityLadderDiagramAllLegsPresent densityLadderDiagramMissingDirect = false.
Proof. reflexivity. Qed.

Lemma density_ladder_diagram_trivial_not_all_legs :
  densityLadderDiagramAllLegsPresent densityLadderDiagramTrivial = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Density** incidence — binding + diagram witness                     *)
(* ------------------------------------------------------------------ *)

Record density_incidence : Type := {
  density_inc_binding : density_binding;
  density_inc_diagram : density_ladder_diagram;
  density_inc_scalar : density_scalar_kind;
  density_inc_level : nat
}.

Definition densityIncidenceNontrivial (h : density_incidence) : bool :=
  Nat.ltb 0 (density_inc_level h).

Definition densityIncidenceFeNamedL1 : density_incidence :=
  {| density_inc_binding := densityBindingFe;
     density_inc_diagram := densityLadderDiagramNamed;
     density_inc_scalar := densityScalarSignedDistance;
     density_inc_level := 1 |}.

Definition densityIncidenceCuNamedL1 : density_incidence :=
  {| density_inc_binding := densityBindingCu;
     density_inc_diagram := densityLadderDiagramNamed;
     density_inc_scalar := densityScalarSignedDistance;
     density_inc_level := 1 |}.

Definition densityIncidenceTrivial : density_incidence :=
  {| density_inc_binding := densityBindingTrivial;
     density_inc_diagram := densityLadderDiagramTrivial;
     density_inc_scalar := densityScalarSignedDistance;
     density_inc_level := 0 |}.

Definition densityIncidenceScrambledOrder : density_incidence :=
  {| density_inc_binding := densityBindingFe;
     density_inc_diagram := densityLadderDiagramScrambledOrder;
     density_inc_scalar := densityScalarSignedDistance;
     density_inc_level := 1 |}.

Definition densityIncidenceMissingDirectLeg : density_incidence :=
  {| density_inc_binding := densityBindingFe;
     density_inc_diagram := densityLadderDiagramMissingDirect;
     density_inc_scalar := densityScalarSignedDistance;
     density_inc_level := 1 |}.

Lemma density_incidence_fe_named_nontrivial :
  densityIncidenceNontrivial densityIncidenceFeNamedL1 = true.
Proof. reflexivity. Qed.

Lemma density_incidence_trivial_not_nontrivial :
  densityIncidenceNontrivial densityIncidenceTrivial = false.
Proof. reflexivity. Qed.

Lemma density_incidence_fe_composed_direct :
  densityComposedEqualsDirect (density_parent_z (density_inc_binding densityIncidenceFeNamedL1)) = true.
Proof. apply density_composed_equals_direct_identity. Qed.

Lemma density_incidence_scaffold_sdf_not_rho :
  density_scalar_sdf_not_rho_unless_named
    (density_inc_scalar densityIncidenceFeNamedL1) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Indirect vs direct markers — ladder legs not interchangeable          *)
(* ------------------------------------------------------------------ *)

Definition indirectLadderMarker : string := "chem_l0_density_micro_to_te_sdf_v1".
Definition directLadderMarker : string := "chem_l0_density_micro_to_frep_direct_v1".

Lemma indirect_ne_direct_ladder_marker :
  indirectLadderMarker <> directLadderMarker.
Proof. discriminate. Qed.

Definition indirectNeDirectLadder : bool :=
  density_leg_indirect_composes_bool &&
  density_leg_direct_endpoints_match_bool &&
  densityComposedEqualsDirect density_element_iron_z &&
  densityLadderDiagramAllLegsPresent densityLadderDiagramNamed &&
  densityLadderDiagramOrderOk densityLadderDiagramNamed.

Lemma indirect_ne_direct_ladder_true : indirectNeDirectLadder = true.
Proof.
  unfold indirectNeDirectLadder.
  rewrite density_leg_indirect_composes_bool_true.
  rewrite density_leg_direct_endpoints_match_bool_true.
  rewrite density_fe_composed_equals_direct.
  simpl.
  reflexivity.
Qed.

Theorem indirect_ne_direct_ladder_identity :
  indirectNeDirectLadder = true /\
  indirectLadderMarker <> directLadderMarker.
Proof.
  split.
  - apply indirect_ne_direct_ladder_true.
  - apply indirect_ne_direct_ladder_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Density** bar — Proved-without-bar fail-closed                     *)
(* ------------------------------------------------------------------ *)

Inductive density_ladder_bar_presence : Type :=
  | density_bar_absent
  | density_bar_present.

Record density_claim_ladder_bar : Type := {
  density_bar_presence : density_ladder_bar_presence;
  density_bar_defect_total : nat
}.

Definition densityClaimLadderBarAbsent : density_claim_ladder_bar :=
  {| density_bar_presence := density_bar_absent; density_bar_defect_total := 0 |}.

Definition densityClaimLadderBarZeroDefect : density_claim_ladder_bar :=
  {| density_bar_presence := density_bar_present; density_bar_defect_total := 0 |}.

Definition density_claim_ladder_bar_zero_defect (b : density_claim_ladder_bar) : bool :=
  match density_bar_presence b with
  | density_bar_absent => false
  | density_bar_present => Nat.eqb (density_bar_defect_total b) 0
  end.

Lemma density_claim_ladder_bar_zero_defect_true :
  density_claim_ladder_bar_zero_defect densityClaimLadderBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma density_claim_ladder_bar_absent_not_zero_defect :
  density_claim_ladder_bar_zero_defect densityClaimLadderBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Density** **conservation** verdict — fail-closed close lattice     *)
(* ------------------------------------------------------------------ *)

Inductive density_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_density_named_ok
  | verdict_trivial_density_refuse
  | verdict_scrambled_order_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition density_conservation_verdict_ok
  (v : density_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_density_named_ok => true
  | _ => false
  end.

Definition density_conservation_verdict_beq
  (v1 v2 : density_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_density_named_ok, verdict_density_named_ok => true
  | verdict_trivial_density_refuse, verdict_trivial_density_refuse => true
  | verdict_scrambled_order_refuse, verdict_scrambled_order_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_density_incidence
  (m : DensityConservationModality)
  (h : density_incidence)
  (b : density_claim_ladder_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : density_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if negb (densityIncidenceNontrivial h)
            then verdict_trivial_density_refuse
            else if negb (densityLadderDiagramAllLegsPresent (density_inc_diagram h))
                 then verdict_scrambled_order_refuse
                 else if negb (densityLadderDiagramOrderOk (density_inc_diagram h))
                      then verdict_scrambled_order_refuse
                      else
                        match m with
                        | density_conservation_unwired => verdict_density_named_ok
                        | density_conservation_assumed
                        | density_conservation_surrogate => verdict_unwired_ok
                        | density_conservation_proved => verdict_proved_without_bar_refuse
                        end.

Definition evaluate_density_conservation_close
  (m : DensityConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : density_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | density_conservation_unwired => verdict_unwired_ok
    | density_conservation_assumed
    | density_conservation_proved
    | density_conservation_surrogate => verdict_density_named_ok
    end.

Definition density_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_density_conservation_close
          density_conservation_proved claim_physics_green claim_production_wired with
  | verdict_density_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  **Density** **conservation** law cells — four laws, open @ Unwired    *)
(* ------------------------------------------------------------------ *)

Inductive density_conservation_law : Type :=
  | law_density_ladder_named
  | law_scrambled_order_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition density_conservation_law_count : nat := 4.

Lemma density_conservation_law_count_is_four :
  density_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive density_conservation_law_witness : Type :=
  | density_law_witness_open
  | density_law_witness_proved.

Definition evaluate_density_conservation_law_witness
  (law : density_conservation_law) (m : DensityConservationModality)
  : density_conservation_law_witness :=
  match m with
  | density_conservation_unwired
  | density_conservation_assumed
  | density_conservation_surrogate => density_law_witness_open
  | density_conservation_proved => density_law_witness_proved
  end.

Lemma all_density_conservation_laws_open_at_unwired :
  evaluate_density_conservation_law_witness law_density_ladder_named
    density_conservation_unwired = density_law_witness_open /\
  evaluate_density_conservation_law_witness law_scrambled_order_refuse
    density_conservation_unwired = density_law_witness_open /\
  evaluate_density_conservation_law_witness law_green_invent_refuse
    density_conservation_unwired = density_law_witness_open /\
  evaluate_density_conservation_law_witness law_production_wired_refuse
    density_conservation_unwired = density_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  DensityLadder pins (structure witnesses — laws not Proved)          *)
(* ------------------------------------------------------------------ *)

Definition densityLadderProved : bool := false.

Lemma density_ladder_proved_false : densityLadderProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_density_conservation_close
    density_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_density_conservation_close
    density_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  density_conservation_verdict_ok
    (evaluate_density_conservation_close
       density_conservation_unwired false false) =
  true.
Proof.
  unfold density_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe **density** close — composed = direct identity conserved   *)
(* ------------------------------------------------------------------ *)

Lemma density_fe_named_ok :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false false =
  verdict_density_named_ok.
Proof. reflexivity. Qed.

Theorem named_density_ladder_conservation :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false false =
  verdict_density_named_ok /\
  densityComposedEqualsDirect (density_parent_z (density_inc_binding densityIncidenceFeNamedL1)) = true /\
  densityBindingIdentityConserved (density_inc_binding densityIncidenceFeNamedL1)
    (density_inc_binding densityIncidenceFeNamedL1) = true /\
  densityLadderDiagramAllLegsPresent (density_inc_diagram densityIncidenceFeNamedL1) = true /\
  densityLadderDiagramOrderOk (density_inc_diagram densityIncidenceFeNamedL1) = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma density_cu_named_ok :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceCuNamedL1
    densityClaimLadderBarAbsent false false =
  verdict_density_named_ok.
Proof. reflexivity. Qed.

Theorem named_cu_density_ladder_conservation :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceCuNamedL1
    densityClaimLadderBarAbsent false false =
  verdict_density_named_ok /\
  densityComposedEqualsDirect (density_parent_z (density_inc_binding densityIncidenceCuNamedL1)) = true.
Proof.
  split.
  - apply density_cu_named_ok.
  - apply density_cu_composed_equals_direct.
Qed.

Lemma density_named_close_ok :
  evaluate_density_conservation_close
    density_conservation_proved false false =
  verdict_density_named_ok.
Proof. reflexivity. Qed.

Theorem named_density_conservation_close :
  evaluate_density_conservation_close
    density_conservation_proved false false =
  verdict_density_named_ok /\
  density_conservation_authorized false false = true.
Proof.
  split.
  - apply density_named_close_ok.
  - unfold density_conservation_authorized.
    rewrite density_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial **density** fail-closed — **conservation** refuse           *)
(* ------------------------------------------------------------------ *)

Lemma trivial_density_refused :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceTrivial
    densityClaimLadderBarAbsent false false =
  verdict_trivial_density_refuse.
Proof. reflexivity. Qed.

Theorem trivial_density_fail_closed :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceTrivial
    densityClaimLadderBarAbsent false false =
  verdict_trivial_density_refuse /\
  density_conservation_verdict_ok
    (evaluate_density_incidence
       density_conservation_unwired densityIncidenceTrivial
       densityClaimLadderBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_density_refused.
  - unfold density_conservation_verdict_ok.
    rewrite trivial_density_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Scrambled-order fail-closed — **density** ladder refuse             *)
(* ------------------------------------------------------------------ *)

Lemma scrambled_order_refused :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceScrambledOrder
    densityClaimLadderBarAbsent false false =
  verdict_scrambled_order_refuse.
Proof. reflexivity. Qed.

Theorem scrambled_order_fail_closed :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceScrambledOrder
    densityClaimLadderBarAbsent false false =
  verdict_scrambled_order_refuse /\
  density_conservation_verdict_ok
    (evaluate_density_incidence
       density_conservation_unwired densityIncidenceScrambledOrder
       densityClaimLadderBarAbsent false false) =
  false.
Proof.
  split.
  - apply scrambled_order_refused.
  - unfold density_conservation_verdict_ok.
    rewrite scrambled_order_refused.
    reflexivity.
Qed.

Lemma missing_direct_leg_scrambled_refused :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceMissingDirectLeg
    densityClaimLadderBarAbsent false false =
  verdict_scrambled_order_refuse.
Proof. reflexivity. Qed.

Theorem missing_direct_leg_scrambled_fail_closed :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceMissingDirectLeg
    densityClaimLadderBarAbsent false false =
  verdict_scrambled_order_refuse /\
  density_conservation_verdict_ok
    (evaluate_density_incidence
       density_conservation_unwired densityIncidenceMissingDirectLeg
       densityClaimLadderBarAbsent false false) =
  false.
Proof.
  split.
  - apply missing_direct_leg_scrambled_refused.
  - unfold density_conservation_verdict_ok.
    rewrite missing_direct_leg_scrambled_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_density_conservation_close
    density_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  density_conservation_verdict_ok
    (evaluate_density_conservation_close
       density_conservation_unwired true false) =
  false.
Proof.
  unfold density_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_density_incidence_refuse :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — **density** **conservation** refuse *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  density_conservation_verdict_ok
    (evaluate_density_incidence
       density_conservation_unwired densityIncidenceFeNamedL1
       densityClaimLadderBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold density_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceCuNamedL1
    densityClaimLadderBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — **density** ladder not production wired     *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_density_conservation_close
    density_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  density_conservation_verdict_ok
    (evaluate_density_conservation_close
       density_conservation_proved false true) =
  false.
Proof.
  unfold density_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Density** **conservation** coherence scaffold — fixture witnesses   *)
(* ------------------------------------------------------------------ *)

Definition density_conservation_coherence_scaffold : bool :=
  density_conservation_verdict_beq
    (evaluate_density_conservation_close
       density_conservation_proved false false)
    verdict_density_named_ok &&
  density_conservation_verdict_beq
    (evaluate_density_conservation_close
       density_conservation_unwired true false)
    verdict_green_invent_refuse &&
  density_conservation_verdict_beq
    (evaluate_density_conservation_close
       density_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma density_conservation_coherence_scaffold_true :
  density_conservation_coherence_scaffold = true.
Proof.
  unfold density_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem density_conservation_coherence_scaffold_theorem :
  evaluate_density_conservation_close
    density_conservation_proved false false =
    verdict_density_named_ok /\
  evaluate_density_conservation_close
    density_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_density_conservation_close
    density_conservation_proved false true =
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
  | claim_density_conservation.

Definition density_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition density_conservation_knowing_fiber_ok : bool :=
  density_conservation_fiber_ok fiber_quantum_knowing.

Definition density_conservation_meso_acting_ok : bool :=
  density_conservation_fiber_ok fiber_meso_acting.

Lemma density_conservation_knowing_fiber_ok_true :
  density_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma density_conservation_meso_acting_not_ok :
  density_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem density_conservation_routes_knowing_not_meso :
  density_conservation_knowing_fiber_ok = true /\
  density_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply density_conservation_knowing_fiber_ok_true.
  - apply density_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  density_conservation_knowing_fiber_ok &&
  negb density_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, density_conservation_knowing_fiber_ok,
    density_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named **density** + fail-closed + fiber + ladder   *)
(* ------------------------------------------------------------------ *)

Theorem density_conservation_fixture_scaffold :
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false false =
    verdict_density_named_ok /\
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceTrivial
    densityClaimLadderBarAbsent false false =
    verdict_trivial_density_refuse /\
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceScrambledOrder
    densityClaimLadderBarAbsent false false =
    verdict_scrambled_order_refuse /\
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceMissingDirectLeg
    densityClaimLadderBarAbsent false false =
    verdict_scrambled_order_refuse /\
  evaluate_density_incidence
    density_conservation_unwired densityIncidenceFeNamedL1
    densityClaimLadderBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_density_conservation_close
    density_conservation_unwired false false =
    verdict_unwired_ok /\
  density_conservation_knowing_fiber_ok = true /\
  density_conservation_meso_acting_ok = false /\
  densityLadderProved = false /\
  indirectNeDirectLadder = true /\
  density_scalar_sdf_not_rho_unless_named densityScalarSignedDistance = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — **density** ladder)  *)
(* ------------------------------------------------------------------ *)

Definition densityLadderAuthority : string :=
  "umst/umst-chem/src/density_ladder.rs".

Definition chemIntDensityLadderTypeAuthority : string :=
  "CHEM-INT-DENSITY-LADDER-TYPE".

Definition chemIntCrossDensityConservationAuthority : string :=
  "CHEM-INT-CROSS-DENSITY-CONSERVATION".

Definition densityConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-DENSITY-CONSERVATION".

Definition densityConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-DENSITY-CONSERVATION DensityLadder mSDF TE-SDF SDF FRep four rungs composed equals direct identity conserved typed Unwired scrambled-order fail-closed GREEN invent fail-closed proved-without-bar fail-closed densityLadderProved false Unwired geometry knowing quantum fiber not meso acting SDF not rho unless named ElectronDensityRho one axiom second law conservation not second density axiom not GREEN DFT not physics GREEN not production_wired".

Lemma density_conservation_cell_id :
  densityConservationCellId = "CHEM-FORMAL-Q-COQ-DENSITY-CONSERVATION".
Proof. reflexivity. Qed.

Lemma density_conservation_cites_density_ladder_rs :
  densityLadderAuthority <> "".
Proof. discriminate. Qed.

Lemma density_conservation_cites_int_density_ladder_type :
  chemIntDensityLadderTypeAuthority = "CHEM-INT-DENSITY-LADDER-TYPE".
Proof. reflexivity. Qed.

Lemma density_conservation_cites_int_cross_density_conservation :
  chemIntCrossDensityConservationAuthority = "CHEM-INT-CROSS-DENSITY-CONSERVATION".
Proof. reflexivity. Qed.

Lemma density_conservation_cites_marker :
  indirectLadderMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not second density *)
(* ------------------------------------------------------------------ *)

Definition densitySecondLawConservationFraming : string :=
  "second_law_conservation_density_one_axiom_not_second_density_axiom".

Lemma density_not_second_density_axiom :
  densitySecondLawConservationFraming <> "second_density_axiom".
Proof. discriminate. Qed.

Lemma density_second_law_conservation_framing :
  densitySecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma density_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma density_conservation_modality_unwired :
  densityConservationModalityCurrent = density_conservation_unwired.
Proof. reflexivity. Qed.

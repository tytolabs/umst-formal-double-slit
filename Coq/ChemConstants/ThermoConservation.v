(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ThermoConservation.v                                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: Thermo_n G(T,P,x) **conservation**.             *)
(*  CALPHAD convex-hull scaffold is the authorized Thermo_n kind;      *)
(*  hull identity conserved. Green Book symbol G; arguments T, P, x    *)
(*  named; composition x mole-fraction scaffold. T-lift ∘ P-lift ∘       *)
(*  x-lift composed equals direct G identity (typed, Unwired — NOT       *)
(*  measured G). formation-zero theater ≠ G fail-closed; measured-scalar *)
(*  G invent fail-closed; scrambled argument-order fail-closed; GREEN    *)
(*  invent fail-closed; Proved-without-bar fail-closed. Live Process G   *)
(*  routes meso/acting (typed witness); this file does NOT mint live G   *)
(*  and does NOT claim Thermo_n Proved. Not 118² GREEN table.            *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  **conservation** framing — hull identity is witness, not second      *)
(*  axiom.                                                               *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Thermo_n G(T,P,x) **conservation** modality (Unwired / Assumed /     *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive ThermoConservationModality : Type :=
  | thermo_conservation_unwired
  | thermo_conservation_assumed
  | thermo_conservation_proved
  | thermo_conservation_surrogate.

Definition thermoConservationModalityCurrent : ThermoConservationModality :=
  thermo_conservation_unwired.

Definition thermo_modality_lattice_cardinality : nat := 4.

Lemma thermo_modality_lattice_cardinality_is_four :
  thermo_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma thermo_modality_lattice_not_118_squared :
  negb (Nat.eqb thermo_modality_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold thermo_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — **thermo** element **conservation** scaffold         *)
(*  (not 118² GREEN table)                                             *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition thermo_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition thermo_element_iron_z : nat := 26.
Definition thermo_element_copper_z : nat := 29.
Definition thermo_element_oganesson_z : nat := 118.

Lemma thermo_iron_z_is_26 :
  thermo_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma thermo_copper_z_is_29 :
  thermo_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma thermo_oganesson_z_is_118 :
  thermo_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma thermo_fe_cu_z_valid :
  thermo_element_z_valid thermo_element_iron_z = true /\
  thermo_element_z_valid thermo_element_copper_z = true.
Proof.
  split; unfold thermo_element_z_valid, thermo_element_iron_z,
    thermo_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma thermo_oganesson_z_valid :
  thermo_element_z_valid thermo_element_oganesson_z = true.
Proof.
  unfold thermo_element_z_valid, thermo_element_oganesson_z, iupac_table_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Thermo_n kind — CALPHAD convex-hull scaffold authorized            *)
(* ------------------------------------------------------------------ *)

Inductive thermo_n_kind : Type :=
  | thermo_n_calphad_convex_hull
  | thermo_n_unauthorized.

Definition thermo_n_kind_beq (k1 k2 : thermo_n_kind) : bool :=
  match k1, k2 with
  | thermo_n_calphad_convex_hull, thermo_n_calphad_convex_hull => true
  | thermo_n_unauthorized, thermo_n_unauthorized => true
  | _, _ => false
  end.

Definition thermoNCalphadConvexHull : thermo_n_kind :=
  thermo_n_calphad_convex_hull.

Definition thermo_n_kind_is_calphad_hull (k : thermo_n_kind) : bool :=
  match k with
  | thermo_n_calphad_convex_hull => true
  | thermo_n_unauthorized => false
  end.

Lemma thermo_n_calphad_hull_authorized :
  thermo_n_kind_is_calphad_hull thermoNCalphadConvexHull = true.
Proof. reflexivity. Qed.

Lemma thermo_n_unauthorized_not_calphad_hull :
  thermo_n_kind_is_calphad_hull thermo_n_unauthorized = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  formation-zero theater ≠ G — Green Book symbol G named              *)
(* ------------------------------------------------------------------ *)

Inductive thermo_g_scalar_kind : Type :=
  | scalar_formation_zero_theater
  | scalar_measured_g_invent
  | scalar_green_book_g.

Definition thermo_g_scalar_kind_beq (k1 k2 : thermo_g_scalar_kind) : bool :=
  match k1, k2 with
  | scalar_formation_zero_theater, scalar_formation_zero_theater => true
  | scalar_measured_g_invent, scalar_measured_g_invent => true
  | scalar_green_book_g, scalar_green_book_g => true
  | _, _ => false
  end.

Definition thermoScalarFormationZeroTheater : thermo_g_scalar_kind :=
  scalar_formation_zero_theater.

Definition thermoScalarMeasuredGInvent : thermo_g_scalar_kind :=
  scalar_measured_g_invent.

Definition thermoScalarGreenBookG : thermo_g_scalar_kind :=
  scalar_green_book_g.

Definition thermo_scalar_is_green_book_g (k : thermo_g_scalar_kind) : bool :=
  match k with
  | scalar_green_book_g => true
  | _ => false
  end.

Definition thermo_scalar_is_formation_zero (k : thermo_g_scalar_kind) : bool :=
  match k with
  | scalar_formation_zero_theater => true
  | _ => false
  end.

Definition thermo_scalar_is_measured_g (k : thermo_g_scalar_kind) : bool :=
  match k with
  | scalar_measured_g_invent => true
  | _ => false
  end.

Definition formation_zero_not_green_book_g : bool :=
  negb (thermo_g_scalar_kind_beq
    thermoScalarFormationZeroTheater thermoScalarGreenBookG).

Lemma formation_zero_theater_not_g :
  formation_zero_not_green_book_g = true.
Proof. reflexivity. Qed.

Lemma thermo_green_book_g_named :
  thermo_scalar_is_green_book_g thermoScalarGreenBookG = true.
Proof. reflexivity. Qed.

Lemma thermo_formation_zero_not_g :
  thermo_scalar_is_green_book_g thermoScalarFormationZeroTheater = false.
Proof. reflexivity. Qed.

Lemma thermo_measured_g_not_green_book :
  thermo_scalar_is_green_book_g thermoScalarMeasuredGInvent = false.
Proof. reflexivity. Qed.

Lemma thermo_formation_zero_is_formation_zero :
  thermo_scalar_is_formation_zero thermoScalarFormationZeroTheater = true.
Proof. reflexivity. Qed.

Lemma thermo_measured_g_is_measured :
  thermo_scalar_is_measured_g thermoScalarMeasuredGInvent = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  G(T,P,x) arguments — T, P, x named; x mole-fraction scaffold       *)
(* ------------------------------------------------------------------ *)

Inductive thermo_argument : Type :=
  | arg_temperature_T
  | arg_pressure_P
  | arg_composition_x.

Definition thermo_argument_beq (a1 a2 : thermo_argument) : bool :=
  match a1, a2 with
  | arg_temperature_T, arg_temperature_T => true
  | arg_pressure_P, arg_pressure_P => true
  | arg_composition_x, arg_composition_x => true
  | _, _ => false
  end.

Definition thermoArgT : thermo_argument := arg_temperature_T.
Definition thermoArgP : thermo_argument := arg_pressure_P.
Definition thermoArgX : thermo_argument := arg_composition_x.

Lemma thermo_arg_T_named :
  thermoArgT = arg_temperature_T.
Proof. reflexivity. Qed.

Lemma thermo_arg_P_named :
  thermoArgP = arg_pressure_P.
Proof. reflexivity. Qed.

Lemma thermo_arg_x_named :
  thermoArgX = arg_composition_x.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Composition x — mole-fraction scaffold                              *)
(* ------------------------------------------------------------------ *)

Record mole_fraction_scaffold : Type := {
  mole_fraction_numerator : nat;
  mole_fraction_denominator : nat
}.

Definition moleFractionUnit : mole_fraction_scaffold :=
  {| mole_fraction_numerator := 1; mole_fraction_denominator := 1 |}.

Definition mole_fraction_scaffold_valid (m : mole_fraction_scaffold) : bool :=
  Nat.ltb 0 (mole_fraction_denominator m) &&
  Nat.leb (mole_fraction_numerator m) (mole_fraction_denominator m).

Lemma mole_fraction_unit_valid :
  mole_fraction_scaffold_valid moleFractionUnit = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  G(T,P,x) legs — T-lift, P-lift, x-lift, direct G                    *)
(* ------------------------------------------------------------------ *)

Inductive thermo_g_leg : Type :=
  | leg_T_lift
  | leg_P_lift
  | leg_x_lift
  | leg_G_direct.

Definition thermo_leg_source (leg : thermo_g_leg) : thermo_argument :=
  match leg with
  | leg_T_lift => arg_temperature_T
  | leg_P_lift => arg_pressure_P
  | leg_x_lift => arg_composition_x
  | leg_G_direct => arg_temperature_T
  end.

Definition thermo_leg_target (leg : thermo_g_leg) : thermo_argument :=
  match leg with
  | leg_T_lift => arg_pressure_P
  | leg_P_lift => arg_composition_x
  | leg_x_lift => arg_composition_x
  | leg_G_direct => arg_composition_x
  end.

Definition thermoLegTLift : thermo_g_leg := leg_T_lift.
Definition thermoLegPLift : thermo_g_leg := leg_P_lift.
Definition thermoLegXLift : thermo_g_leg := leg_x_lift.
Definition thermoLegGDirect : thermo_g_leg := leg_G_direct.

Lemma thermo_leg_T_lift_named :
  thermoLegTLift = leg_T_lift.
Proof. reflexivity. Qed.

Lemma thermo_leg_P_lift_named :
  thermoLegPLift = leg_P_lift.
Proof. reflexivity. Qed.

Lemma thermo_leg_x_lift_named :
  thermoLegXLift = leg_x_lift.
Proof. reflexivity. Qed.

Lemma thermo_leg_G_direct_named :
  thermoLegGDirect = leg_G_direct.
Proof. reflexivity. Qed.

Definition thermo_leg_indirect_composes_bool : bool :=
  thermo_argument_beq
    (thermo_leg_target thermoLegTLift)
    (thermo_leg_source thermoLegPLift) &&
  thermo_argument_beq
    (thermo_leg_target thermoLegPLift)
    (thermo_leg_source thermoLegXLift).

Definition thermo_leg_direct_endpoints_match_bool : bool :=
  thermo_argument_beq
    (thermo_leg_source thermoLegTLift)
    (thermo_leg_source thermoLegGDirect) &&
  thermo_argument_beq
    (thermo_leg_target thermoLegXLift)
    (thermo_leg_target thermoLegGDirect).

Lemma thermo_leg_indirect_composes_args :
  thermo_leg_target thermoLegTLift = thermo_leg_source thermoLegPLift /\
  thermo_leg_target thermoLegPLift = thermo_leg_source thermoLegXLift.
Proof. tauto. Qed.

Lemma thermo_leg_indirect_composes_bool_true :
  thermo_leg_indirect_composes_bool = true.
Proof. reflexivity. Qed.

Lemma thermo_leg_direct_endpoints_match :
  thermo_leg_source thermoLegTLift =
    thermo_leg_source thermoLegGDirect /\
  thermo_leg_target thermoLegXLift =
    thermo_leg_target thermoLegGDirect.
Proof. tauto. Qed.

Lemma thermo_leg_direct_endpoints_match_bool_true :
  thermo_leg_direct_endpoints_match_bool = true.
Proof. reflexivity. Qed.

Lemma thermo_leg_distinct_T_vs_P :
  negb (thermo_argument_beq
    (thermo_leg_source thermoLegTLift)
    (thermo_leg_target thermoLegTLift)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Thermo** binding — parent Z identity across G legs               *)
(* ------------------------------------------------------------------ *)

Record thermo_binding : Type := {
  thermo_parent_z : nat
}.

Definition thermoBindingFe : thermo_binding :=
  {| thermo_parent_z := thermo_element_iron_z |}.

Definition thermoBindingCu : thermo_binding :=
  {| thermo_parent_z := thermo_element_copper_z |}.

Definition thermoBindingOg : thermo_binding :=
  {| thermo_parent_z := thermo_element_oganesson_z |}.

Definition thermoBindingTrivial : thermo_binding :=
  {| thermo_parent_z := 0 |}.

Definition thermoBindingNontrivial (b : thermo_binding) : bool :=
  Nat.ltb 0 (thermo_parent_z b).

Lemma thermo_binding_fe_nontrivial :
  thermoBindingNontrivial thermoBindingFe = true.
Proof. reflexivity. Qed.

Lemma thermo_binding_trivial_not_nontrivial :
  thermoBindingNontrivial thermoBindingTrivial = false.
Proof. reflexivity. Qed.

Definition thermoBindingIdentityConserved (b1 b2 : thermo_binding) : bool :=
  Nat.eqb (thermo_parent_z b1) (thermo_parent_z b2).

Lemma thermo_binding_fe_identity_conserved :
  thermoBindingIdentityConserved thermoBindingFe thermoBindingFe = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  G(T,P,x) leg lifts — typed identity placeholders (Unwired)          *)
(* ------------------------------------------------------------------ *)

Definition liftT (z : nat) : nat := z.

Definition liftP (z : nat) : nat := z.

Definition liftX (z : nat) : nat := z.

Definition liftGDirect (z : nat) : nat := z.

Lemma lift_T_identity (z : nat) :
  liftT z = z.
Proof. reflexivity. Qed.

Lemma lift_P_identity (z : nat) :
  liftP z = z.
Proof. reflexivity. Qed.

Lemma lift_x_identity (z : nat) :
  liftX z = z.
Proof. reflexivity. Qed.

Lemma lift_G_direct_identity (z : nat) :
  liftGDirect z = z.
Proof. reflexivity. Qed.

Definition thermoComposedIdentity (z : nat) : nat :=
  liftX (liftP (liftT z)).

Definition thermoDirectIdentity (z : nat) : nat :=
  liftGDirect z.

Definition thermoComposedEqualsDirect (z : nat) : bool :=
  Nat.eqb (thermoComposedIdentity z) (thermoDirectIdentity z).

Lemma thermo_composed_equals_direct_identity (z : nat) :
  thermoComposedEqualsDirect z = true.
Proof.
  unfold thermoComposedEqualsDirect, thermoComposedIdentity, thermoDirectIdentity,
    liftX, liftP, liftT, liftGDirect.
  apply Nat.eqb_refl.
Qed.

Theorem thermo_g_identity_conserved :
  forall z : nat,
    thermoComposedIdentity z = thermoDirectIdentity z.
Proof.
  intros z.
  reflexivity.
Qed.

Lemma thermo_fe_composed_equals_direct :
  thermoComposedEqualsDirect thermo_element_iron_z = true.
Proof. apply thermo_composed_equals_direct_identity. Qed.

Lemma thermo_cu_composed_equals_direct :
  thermoComposedEqualsDirect thermo_element_copper_z = true.
Proof. apply thermo_composed_equals_direct_identity. Qed.

(* ------------------------------------------------------------------ *)
(*  G(T,P,x) diagram — T, P, x legs named (scaffold)                    *)
(* ------------------------------------------------------------------ *)

Record thermo_g_diagram : Type := {
  via_T : thermo_g_leg;
  then_P : thermo_g_leg;
  then_x : thermo_g_leg;
  direct_G : thermo_g_leg;
  has_T_lift : bool;
  has_P_lift : bool;
  has_x_lift : bool;
  has_G_direct : bool
}.

Definition thermoGDiagramNamed : thermo_g_diagram :=
  {| via_T := thermoLegTLift;
     then_P := thermoLegPLift;
     then_x := thermoLegXLift;
     direct_G := thermoLegGDirect;
     has_T_lift := true;
     has_P_lift := true;
     has_x_lift := true;
     has_G_direct := true |}.

Definition thermoGDiagramMissingDirect : thermo_g_diagram :=
  {| via_T := thermoLegTLift;
     then_P := thermoLegPLift;
     then_x := thermoLegXLift;
     direct_G := thermoLegGDirect;
     has_T_lift := true;
     has_P_lift := true;
     has_x_lift := true;
     has_G_direct := false |}.

Definition thermoGDiagramScrambledOrder : thermo_g_diagram :=
  {| via_T := thermoLegXLift;
     then_P := thermoLegPLift;
     then_x := thermoLegTLift;
     direct_G := thermoLegGDirect;
     has_T_lift := true;
     has_P_lift := true;
     has_x_lift := true;
     has_G_direct := true |}.

Definition thermoGDiagramTrivial : thermo_g_diagram :=
  {| via_T := thermoLegTLift;
     then_P := thermoLegPLift;
     then_x := thermoLegXLift;
     direct_G := thermoLegGDirect;
     has_T_lift := false;
     has_P_lift := false;
     has_x_lift := false;
     has_G_direct := false |}.

Definition thermoGDiagramAllLegsPresent (d : thermo_g_diagram) : bool :=
  d.(has_T_lift) &&
  d.(has_P_lift) &&
  d.(has_x_lift) &&
  d.(has_G_direct).

Definition thermoGDiagramLegsNamed (d : thermo_g_diagram) : bool :=
  thermo_argument_beq (thermo_leg_source d.(via_T)) arg_temperature_T &&
  thermo_argument_beq (thermo_leg_target d.(via_T)) arg_pressure_P &&
  thermo_argument_beq (thermo_leg_source d.(then_P)) arg_pressure_P &&
  thermo_argument_beq (thermo_leg_target d.(then_P)) arg_composition_x &&
  thermo_argument_beq (thermo_leg_source d.(then_x)) arg_composition_x &&
  thermo_argument_beq (thermo_leg_target d.(then_x)) arg_composition_x &&
  thermo_argument_beq (thermo_leg_source d.(direct_G)) arg_temperature_T &&
  thermo_argument_beq (thermo_leg_target d.(direct_G)) arg_composition_x.

Definition thermoGDiagramOrderOk (d : thermo_g_diagram) : bool :=
  thermo_argument_beq
    (thermo_leg_target d.(via_T))
    (thermo_leg_source d.(then_P)) &&
  thermo_argument_beq
    (thermo_leg_target d.(then_P))
    (thermo_leg_source d.(then_x)) &&
  thermo_argument_beq
    (thermo_leg_source d.(via_T))
    (thermo_leg_source d.(direct_G)) &&
  thermo_argument_beq
    (thermo_leg_target d.(then_x))
    (thermo_leg_target d.(direct_G)).

Lemma thermo_g_diagram_named_all_legs :
  thermoGDiagramAllLegsPresent thermoGDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma thermo_g_diagram_named_legs_named :
  thermoGDiagramLegsNamed thermoGDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma thermo_g_diagram_named_order_ok :
  thermoGDiagramOrderOk thermoGDiagramNamed = true.
Proof. reflexivity. Qed.

Lemma thermo_g_diagram_scrambled_order_not_ok :
  thermoGDiagramOrderOk thermoGDiagramScrambledOrder = false.
Proof. reflexivity. Qed.

Lemma thermo_g_diagram_missing_direct_not_all_legs :
  thermoGDiagramAllLegsPresent thermoGDiagramMissingDirect = false.
Proof. reflexivity. Qed.

Lemma thermo_g_diagram_trivial_not_all_legs :
  thermoGDiagramAllLegsPresent thermoGDiagramTrivial = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Thermo** incidence — binding + diagram + scalar + Thermo_n kind   *)
(* ------------------------------------------------------------------ *)

Record thermo_incidence : Type := {
  thermo_inc_binding : thermo_binding;
  thermo_inc_diagram : thermo_g_diagram;
  thermo_inc_scalar : thermo_g_scalar_kind;
  thermo_inc_thermo_n_kind : thermo_n_kind;
  thermo_inc_mole_fraction : mole_fraction_scaffold;
  thermo_inc_level : nat
}.

Definition thermoIncidenceNontrivial (h : thermo_incidence) : bool :=
  Nat.ltb 0 (thermo_inc_level h).

Definition thermoIncidenceFeNamedL1 : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingFe;
     thermo_inc_diagram := thermoGDiagramNamed;
     thermo_inc_scalar := thermoScalarGreenBookG;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Definition thermoIncidenceCuNamedL1 : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingCu;
     thermo_inc_diagram := thermoGDiagramNamed;
     thermo_inc_scalar := thermoScalarGreenBookG;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Definition thermoIncidenceTrivial : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingTrivial;
     thermo_inc_diagram := thermoGDiagramTrivial;
     thermo_inc_scalar := thermoScalarGreenBookG;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 0 |}.

Definition thermoIncidenceScrambledOrder : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingFe;
     thermo_inc_diagram := thermoGDiagramScrambledOrder;
     thermo_inc_scalar := thermoScalarGreenBookG;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Definition thermoIncidenceMissingDirectLeg : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingFe;
     thermo_inc_diagram := thermoGDiagramMissingDirect;
     thermo_inc_scalar := thermoScalarGreenBookG;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Definition thermoIncidenceFormationZero : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingFe;
     thermo_inc_diagram := thermoGDiagramNamed;
     thermo_inc_scalar := thermoScalarFormationZeroTheater;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Definition thermoIncidenceMeasuredG : thermo_incidence :=
  {| thermo_inc_binding := thermoBindingFe;
     thermo_inc_diagram := thermoGDiagramNamed;
     thermo_inc_scalar := thermoScalarMeasuredGInvent;
     thermo_inc_thermo_n_kind := thermoNCalphadConvexHull;
     thermo_inc_mole_fraction := moleFractionUnit;
     thermo_inc_level := 1 |}.

Lemma thermo_incidence_fe_named_nontrivial :
  thermoIncidenceNontrivial thermoIncidenceFeNamedL1 = true.
Proof. reflexivity. Qed.

Lemma thermo_incidence_trivial_not_nontrivial :
  thermoIncidenceNontrivial thermoIncidenceTrivial = false.
Proof. reflexivity. Qed.

Lemma thermo_incidence_fe_composed_direct :
  thermoComposedEqualsDirect (thermo_parent_z (thermo_inc_binding thermoIncidenceFeNamedL1)) = true.
Proof. apply thermo_composed_equals_direct_identity. Qed.

Lemma thermo_incidence_calphad_hull_kind :
  thermo_n_kind_is_calphad_hull
    (thermo_inc_thermo_n_kind thermoIncidenceFeNamedL1) = true.
Proof. reflexivity. Qed.

Lemma thermo_incidence_green_book_g :
  thermo_scalar_is_green_book_g
    (thermo_inc_scalar thermoIncidenceFeNamedL1) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Indirect vs direct markers — G legs not interchangeable             *)
(* ------------------------------------------------------------------ *)

Definition indirectThermoMarker : string := "chem_l0_thermo_T_P_x_v1".
Definition directThermoMarker : string := "chem_l0_thermo_G_direct_v1".

Lemma indirect_ne_direct_thermo_marker :
  indirectThermoMarker <> directThermoMarker.
Proof. discriminate. Qed.

Definition indirectNeDirectThermo : bool :=
  thermo_leg_indirect_composes_bool &&
  thermo_leg_direct_endpoints_match_bool &&
  thermoComposedEqualsDirect thermo_element_iron_z &&
  thermoGDiagramAllLegsPresent thermoGDiagramNamed &&
  thermoGDiagramOrderOk thermoGDiagramNamed.

Lemma indirect_ne_direct_thermo_true : indirectNeDirectThermo = true.
Proof.
  unfold indirectNeDirectThermo.
  rewrite thermo_leg_indirect_composes_bool_true.
  rewrite thermo_leg_direct_endpoints_match_bool_true.
  rewrite thermo_fe_composed_equals_direct.
  simpl.
  reflexivity.
Qed.

Theorem indirect_ne_direct_thermo_identity :
  indirectNeDirectThermo = true /\
  indirectThermoMarker <> directThermoMarker.
Proof.
  split.
  - apply indirect_ne_direct_thermo_true.
  - apply indirect_ne_direct_thermo_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Thermo** bar — Proved-without-bar fail-closed                     *)
(* ------------------------------------------------------------------ *)

Inductive thermo_g_bar_presence : Type :=
  | thermo_bar_absent
  | thermo_bar_present.

Record thermo_claim_g_bar : Type := {
  thermo_bar_presence : thermo_g_bar_presence;
  thermo_bar_defect_total : nat
}.

Definition thermoClaimGBarAbsent : thermo_claim_g_bar :=
  {| thermo_bar_presence := thermo_bar_absent; thermo_bar_defect_total := 0 |}.

Definition thermoClaimGBarZeroDefect : thermo_claim_g_bar :=
  {| thermo_bar_presence := thermo_bar_present; thermo_bar_defect_total := 0 |}.

Definition thermo_claim_g_bar_zero_defect (b : thermo_claim_g_bar) : bool :=
  match thermo_bar_presence b with
  | thermo_bar_absent => false
  | thermo_bar_present => Nat.eqb (thermo_bar_defect_total b) 0
  end.

Lemma thermo_claim_g_bar_zero_defect_true :
  thermo_claim_g_bar_zero_defect thermoClaimGBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma thermo_claim_g_bar_absent_not_zero_defect :
  thermo_claim_g_bar_zero_defect thermoClaimGBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  **Thermo** **conservation** verdict — fail-closed close lattice     *)
(* ------------------------------------------------------------------ *)

Inductive thermo_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_thermo_named_ok
  | verdict_trivial_thermo_refuse
  | verdict_scrambled_order_refuse
  | verdict_formation_zero_refuse
  | verdict_measured_g_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition thermo_conservation_verdict_ok
  (v : thermo_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_thermo_named_ok => true
  | _ => false
  end.

Definition thermo_conservation_verdict_beq
  (v1 v2 : thermo_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_thermo_named_ok, verdict_thermo_named_ok => true
  | verdict_trivial_thermo_refuse, verdict_trivial_thermo_refuse => true
  | verdict_scrambled_order_refuse, verdict_scrambled_order_refuse => true
  | verdict_formation_zero_refuse, verdict_formation_zero_refuse => true
  | verdict_measured_g_refuse, verdict_measured_g_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_thermo_incidence
  (m : ThermoConservationModality)
  (h : thermo_incidence)
  (b : thermo_claim_g_bar)
  (claim_physics_green : bool)
  (claim_proved : bool) : thermo_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if thermo_scalar_is_formation_zero (thermo_inc_scalar h)
            then verdict_formation_zero_refuse
            else if thermo_scalar_is_measured_g (thermo_inc_scalar h)
                 then verdict_measured_g_refuse
                 else if negb (thermoIncidenceNontrivial h)
                      then verdict_trivial_thermo_refuse
                      else if negb (thermoGDiagramAllLegsPresent (thermo_inc_diagram h))
                           then verdict_scrambled_order_refuse
                           else if negb (thermoGDiagramOrderOk (thermo_inc_diagram h))
                                then verdict_scrambled_order_refuse
                                else
                                  match m with
                                  | thermo_conservation_unwired => verdict_thermo_named_ok
                                  | thermo_conservation_assumed
                                  | thermo_conservation_surrogate => verdict_unwired_ok
                                  | thermo_conservation_proved => verdict_proved_without_bar_refuse
                                  end.

Definition evaluate_thermo_conservation_close
  (m : ThermoConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : thermo_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | thermo_conservation_unwired => verdict_unwired_ok
    | thermo_conservation_assumed
    | thermo_conservation_proved
    | thermo_conservation_surrogate => verdict_thermo_named_ok
    end.

Definition thermo_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_thermo_conservation_close
          thermo_conservation_proved claim_physics_green claim_production_wired with
  | verdict_thermo_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  **Thermo** **conservation** law cells — four laws, open @ Unwired    *)
(* ------------------------------------------------------------------ *)

Inductive thermo_conservation_law : Type :=
  | law_thermo_g_named
  | law_scrambled_order_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition thermo_conservation_law_count : nat := 4.

Lemma thermo_conservation_law_count_is_four :
  thermo_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive thermo_conservation_law_witness : Type :=
  | thermo_law_witness_open
  | thermo_law_witness_proved.

Definition evaluate_thermo_conservation_law_witness
  (law : thermo_conservation_law) (m : ThermoConservationModality)
  : thermo_conservation_law_witness :=
  match m with
  | thermo_conservation_unwired
  | thermo_conservation_assumed
  | thermo_conservation_surrogate => thermo_law_witness_open
  | thermo_conservation_proved => thermo_law_witness_proved
  end.

Lemma all_thermo_conservation_laws_open_at_unwired :
  evaluate_thermo_conservation_law_witness law_thermo_g_named
    thermo_conservation_unwired = thermo_law_witness_open /\
  evaluate_thermo_conservation_law_witness law_scrambled_order_refuse
    thermo_conservation_unwired = thermo_law_witness_open /\
  evaluate_thermo_conservation_law_witness law_green_invent_refuse
    thermo_conservation_unwired = thermo_law_witness_open /\
  evaluate_thermo_conservation_law_witness law_production_wired_refuse
    thermo_conservation_unwired = thermo_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Thermo_n pins (structure witnesses — laws not Proved)             *)
(* ------------------------------------------------------------------ *)

Definition thermoGProved : bool := false.

Lemma thermo_g_proved_false : thermoGProved = false.
Proof. reflexivity. Qed.

Definition thermoNProved : bool := false.

Lemma thermo_n_proved_false : thermoNProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_thermo_conservation_close
    thermo_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_thermo_conservation_close
    thermo_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  thermo_conservation_verdict_ok
    (evaluate_thermo_conservation_close
       thermo_conservation_unwired false false) =
  true.
Proof.
  unfold thermo_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe **thermo** close — composed = direct identity conserved    *)
(* ------------------------------------------------------------------ *)

Lemma thermo_fe_named_ok :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false false =
  verdict_thermo_named_ok.
Proof. reflexivity. Qed.

Theorem named_thermo_g_conservation :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false false =
  verdict_thermo_named_ok /\
  thermoComposedEqualsDirect (thermo_parent_z (thermo_inc_binding thermoIncidenceFeNamedL1)) = true /\
  thermoBindingIdentityConserved (thermo_inc_binding thermoIncidenceFeNamedL1)
    (thermo_inc_binding thermoIncidenceFeNamedL1) = true /\
  thermoGDiagramAllLegsPresent (thermo_inc_diagram thermoIncidenceFeNamedL1) = true /\
  thermoGDiagramOrderOk (thermo_inc_diagram thermoIncidenceFeNamedL1) = true /\
  thermo_n_kind_is_calphad_hull (thermo_inc_thermo_n_kind thermoIncidenceFeNamedL1) = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma thermo_cu_named_ok :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceCuNamedL1
    thermoClaimGBarAbsent false false =
  verdict_thermo_named_ok.
Proof. reflexivity. Qed.

Theorem named_cu_thermo_g_conservation :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceCuNamedL1
    thermoClaimGBarAbsent false false =
  verdict_thermo_named_ok /\
  thermoComposedEqualsDirect (thermo_parent_z (thermo_inc_binding thermoIncidenceCuNamedL1)) = true.
Proof.
  split.
  - apply thermo_cu_named_ok.
  - apply thermo_cu_composed_equals_direct.
Qed.

Lemma thermo_named_close_ok :
  evaluate_thermo_conservation_close
    thermo_conservation_proved false false =
  verdict_thermo_named_ok.
Proof. reflexivity. Qed.

Theorem named_thermo_conservation_close :
  evaluate_thermo_conservation_close
    thermo_conservation_proved false false =
  verdict_thermo_named_ok /\
  thermo_conservation_authorized false false = true.
Proof.
  split.
  - apply thermo_named_close_ok.
  - unfold thermo_conservation_authorized.
    rewrite thermo_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial **thermo** fail-closed — **conservation** refuse            *)
(* ------------------------------------------------------------------ *)

Lemma trivial_thermo_refused :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceTrivial
    thermoClaimGBarAbsent false false =
  verdict_trivial_thermo_refuse.
Proof. reflexivity. Qed.

Theorem trivial_thermo_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceTrivial
    thermoClaimGBarAbsent false false =
  verdict_trivial_thermo_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceTrivial
       thermoClaimGBarAbsent false false) =
  false.
Proof.
  split.
  - apply trivial_thermo_refused.
  - unfold thermo_conservation_verdict_ok.
    rewrite trivial_thermo_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Scrambled-order fail-closed — **thermo** G refuse                   *)
(* ------------------------------------------------------------------ *)

Lemma scrambled_order_refused :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceScrambledOrder
    thermoClaimGBarAbsent false false =
  verdict_scrambled_order_refuse.
Proof. reflexivity. Qed.

Theorem scrambled_order_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceScrambledOrder
    thermoClaimGBarAbsent false false =
  verdict_scrambled_order_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceScrambledOrder
       thermoClaimGBarAbsent false false) =
  false.
Proof.
  split.
  - apply scrambled_order_refused.
  - unfold thermo_conservation_verdict_ok.
    rewrite scrambled_order_refused.
    reflexivity.
Qed.

Lemma missing_direct_leg_scrambled_refused :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMissingDirectLeg
    thermoClaimGBarAbsent false false =
  verdict_scrambled_order_refuse.
Proof. reflexivity. Qed.

Theorem missing_direct_leg_scrambled_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMissingDirectLeg
    thermoClaimGBarAbsent false false =
  verdict_scrambled_order_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceMissingDirectLeg
       thermoClaimGBarAbsent false false) =
  false.
Proof.
  split.
  - apply missing_direct_leg_scrambled_refused.
  - unfold thermo_conservation_verdict_ok.
    rewrite missing_direct_leg_scrambled_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  formation-zero theater ≠ G fail-closed                              *)
(* ------------------------------------------------------------------ *)

Lemma formation_zero_refused :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFormationZero
    thermoClaimGBarAbsent false false =
  verdict_formation_zero_refuse.
Proof. reflexivity. Qed.

Theorem formation_zero_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFormationZero
    thermoClaimGBarAbsent false false =
  verdict_formation_zero_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceFormationZero
       thermoClaimGBarAbsent false false) =
  false.
Proof.
  split.
  - apply formation_zero_refused.
  - unfold thermo_conservation_verdict_ok.
    rewrite formation_zero_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  measured-scalar G invent refuse fail-closed                         *)
(* ------------------------------------------------------------------ *)

Lemma measured_g_refused :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMeasuredG
    thermoClaimGBarAbsent false false =
  verdict_measured_g_refuse.
Proof. reflexivity. Qed.

Theorem measured_g_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMeasuredG
    thermoClaimGBarAbsent false false =
  verdict_measured_g_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceMeasuredG
       thermoClaimGBarAbsent false false) =
  false.
Proof.
  split.
  - apply measured_g_refused.
  - unfold thermo_conservation_verdict_ok.
    rewrite measured_g_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_thermo_conservation_close
    thermo_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  thermo_conservation_verdict_ok
    (evaluate_thermo_conservation_close
       thermo_conservation_unwired true false) =
  false.
Proof.
  unfold thermo_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_thermo_incidence_refuse :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — **thermo** **conservation** refuse *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false true =
  verdict_proved_without_bar_refuse /\
  thermo_conservation_verdict_ok
    (evaluate_thermo_incidence
       thermo_conservation_unwired thermoIncidenceFeNamedL1
       thermoClaimGBarAbsent false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold thermo_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

Lemma proved_without_bar_zero_defect_still_refuse :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceCuNamedL1
    thermoClaimGBarZeroDefect false true =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — **thermo** G not production wired         *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_thermo_conservation_close
    thermo_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  thermo_conservation_verdict_ok
    (evaluate_thermo_conservation_close
       thermo_conservation_proved false true) =
  false.
Proof.
  unfold thermo_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Thermo** **conservation** coherence scaffold — fixture witnesses   *)
(* ------------------------------------------------------------------ *)

Definition thermo_conservation_coherence_scaffold : bool :=
  thermo_conservation_verdict_beq
    (evaluate_thermo_conservation_close
       thermo_conservation_proved false false)
    verdict_thermo_named_ok &&
  thermo_conservation_verdict_beq
    (evaluate_thermo_conservation_close
       thermo_conservation_unwired true false)
    verdict_green_invent_refuse &&
  thermo_conservation_verdict_beq
    (evaluate_thermo_conservation_close
       thermo_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma thermo_conservation_coherence_scaffold_true :
  thermo_conservation_coherence_scaffold = true.
Proof.
  unfold thermo_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem thermo_conservation_coherence_scaffold_theorem :
  evaluate_thermo_conservation_close
    thermo_conservation_proved false false =
    verdict_thermo_named_ok /\
  evaluate_thermo_conservation_close
    thermo_conservation_unwired true false =
    verdict_green_invent_refuse /\
  evaluate_thermo_conservation_close
    thermo_conservation_proved false true =
    verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Live Process G routing — meso/acting (NOT knowing-fiber mint)       *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_thermo_conservation.

Definition thermo_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_meso_acting => true
  | fiber_quantum_knowing => false
  end.

Definition thermo_conservation_meso_acting_ok : bool :=
  thermo_conservation_fiber_ok fiber_meso_acting.

Definition thermo_conservation_knowing_fiber_ok : bool :=
  thermo_conservation_fiber_ok fiber_quantum_knowing.

Definition thermoDoesNotMintLiveG : bool :=
  negb thermo_conservation_knowing_fiber_ok.

Definition thermoDoesNotClaimThermoNProved : bool :=
  negb thermoNProved.

Lemma thermo_conservation_meso_acting_ok_true :
  thermo_conservation_meso_acting_ok = true.
Proof. reflexivity. Qed.

Lemma thermo_conservation_knowing_fiber_not_ok :
  thermo_conservation_knowing_fiber_ok = false.
Proof. reflexivity. Qed.

Theorem thermo_conservation_routes_meso_not_knowing :
  thermo_conservation_meso_acting_ok = true /\
  thermo_conservation_knowing_fiber_ok = false /\
  thermoDoesNotMintLiveG = true /\
  thermoDoesNotClaimThermoNProved = true.
Proof.
  repeat split; reflexivity.
Qed.

Definition fiberMesoActingNotKnowing : bool :=
  thermo_conservation_meso_acting_ok &&
  negb thermo_conservation_knowing_fiber_ok.

Lemma fiber_meso_acting_not_knowing_true : fiberMesoActingNotKnowing = true.
Proof.
  unfold fiberMesoActingNotKnowing, thermo_conservation_meso_acting_ok,
    thermo_conservation_knowing_fiber_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named **thermo** + fail-closed + fiber + G legs  *)
(* ------------------------------------------------------------------ *)

Theorem thermo_conservation_fixture_scaffold :
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false false =
    verdict_thermo_named_ok /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceTrivial
    thermoClaimGBarAbsent false false =
    verdict_trivial_thermo_refuse /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceScrambledOrder
    thermoClaimGBarAbsent false false =
    verdict_scrambled_order_refuse /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMissingDirectLeg
    thermoClaimGBarAbsent false false =
    verdict_scrambled_order_refuse /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFormationZero
    thermoClaimGBarAbsent false false =
    verdict_formation_zero_refuse /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceMeasuredG
    thermoClaimGBarAbsent false false =
    verdict_measured_g_refuse /\
  evaluate_thermo_incidence
    thermo_conservation_unwired thermoIncidenceFeNamedL1
    thermoClaimGBarAbsent false true =
    verdict_proved_without_bar_refuse /\
  evaluate_thermo_conservation_close
    thermo_conservation_unwired false false =
    verdict_unwired_ok /\
  thermo_conservation_meso_acting_ok = true /\
  thermo_conservation_knowing_fiber_ok = false /\
  thermoGProved = false /\
  thermoNProved = false /\
  indirectNeDirectThermo = true /\
  formation_zero_not_green_book_g = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — **thermo** G)        *)
(* ------------------------------------------------------------------ *)

Definition thermoGAuthority : string :=
  "umst/umst-chem/src/thermo_g.rs".

Definition chemIntThermoNTypeAuthority : string :=
  "CHEM-INT-THERMO-N-TYPE".

Definition chemIntCrossThermoConservationAuthority : string :=
  "CHEM-INT-CROSS-THERMO-CONSERVATION".

Definition thermoConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-THERMO-CONSERVATION".

Definition thermoConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-THERMO-CONSERVATION Thermo_n G(T,P,x) CALPHAD convex-hull hull identity conserved typed Unwired T-lift P-lift x-lift composed equals direct G identity conserved formation-zero theater not G measured-scalar G invent refuse scrambled-order fail-closed GREEN invent fail-closed proved-without-bar fail-closed thermoGProved false thermoNProved false Unwired Live Process G routes meso acting not knowing fiber does not mint live G does not claim Thermo_n Proved one axiom second law conservation hull identity witness not second axiom not GREEN not physics GREEN not production_wired".

Lemma thermo_conservation_cell_id :
  thermoConservationCellId = "CHEM-FORMAL-Q-COQ-THERMO-CONSERVATION".
Proof. reflexivity. Qed.

Lemma thermo_conservation_cites_thermo_g_rs :
  thermoGAuthority <> "".
Proof. discriminate. Qed.

Lemma thermo_conservation_cites_int_thermo_n_type :
  chemIntThermoNTypeAuthority = "CHEM-INT-THERMO-N-TYPE".
Proof. reflexivity. Qed.

Lemma thermo_conservation_cites_int_cross_thermo_conservation :
  chemIntCrossThermoConservationAuthority = "CHEM-INT-CROSS-THERMO-CONSERVATION".
Proof. reflexivity. Qed.

Lemma thermo_conservation_cites_marker :
  indirectThermoMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; hull witness       *)
(* ------------------------------------------------------------------ *)

Definition thermoSecondLawConservationFraming : string :=
  "second_law_conservation_thermo_one_axiom_hull_identity_witness_not_second_axiom".

Lemma thermo_not_second_thermo_axiom :
  thermoSecondLawConservationFraming <> "second_thermo_axiom".
Proof. discriminate. Qed.

Lemma thermo_second_law_conservation_framing :
  thermoSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma thermo_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma thermo_conservation_modality_unwired :
  thermoConservationModalityCurrent = thermo_conservation_unwired.
Proof. reflexivity. Qed.

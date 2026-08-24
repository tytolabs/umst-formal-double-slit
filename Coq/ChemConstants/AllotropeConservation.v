(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AllotropeConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: pattern class **allotrope** **conservation**.   *)
(*  Same IUPAC Z, many geometry variants (C diamond/graphite; P       *)
(*  white/red; O O₂/O₃) — ElementId **conserved**, Geometry_n varies.  *)
(*  Class 10 concurrent Π_c PatternBundle factor — not XOR enum; not a  *)
(*  26th axiom / not fourth chemistry science. Not Xe-copy (no Z=54     *)
(*  relativistic continuum theater). GREEN invent fail-closed;           *)
(*  Proved-without-bar fail-closed; trivial Z=0 refuse.                  *)
(*  allotropeProved false. Modality Unwired.                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Allotrope **conservation** modality (Unwired / Assumed / Proved /   *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive AllotropeConservationModality : Type :=
  | allotrope_conservation_unwired
  | allotrope_conservation_assumed
  | allotrope_conservation_proved
  | allotrope_conservation_surrogate.

Definition allotropeConservationModalityCurrent : AllotropeConservationModality :=
  allotrope_conservation_unwired.

Definition allotrope_modality_lattice_cardinality : nat := 4.

Lemma allotrope_modality_lattice_cardinality_is_four :
  allotrope_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma allotrope_modality_lattice_not_118_squared :
  negb (Nat.eqb allotrope_modality_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold allotrope_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern class 10 — allotrope concurrent Π_c factor (not XOR)         *)
(* ------------------------------------------------------------------ *)

Definition pattern_class_allotrope_idx : nat := 10.

Lemma pattern_class_allotrope_idx_is_10 :
  pattern_class_allotrope_idx = 10.
Proof. reflexivity. Qed.

Definition pattern_class_cardinality : nat := 25.

Lemma pattern_class_cardinality_is_25 :
  pattern_class_cardinality = 25.
Proof. reflexivity. Qed.

Definition pattern_class_index_valid (i : nat) : bool :=
  Nat.ltb i pattern_class_cardinality.

Lemma allotrope_class_index_valid :
  pattern_class_index_valid pattern_class_allotrope_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_allotrope_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierAllotropeRowId : string := "X10".

Lemma cross_classifier_allotrope_row_named :
  crossClassifierAllotropeRowId = "X10".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — element **conservation** scaffold (not 118² table)   *)
(*  Witnesses: C Z=6, P Z=15, O Z=8 — not Xe Z=54 copy theater.         *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition allotrope_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition allotrope_element_carbon_z : nat := 6.
Definition allotrope_element_phosphorus_z : nat := 15.
Definition allotrope_element_oxygen_z : nat := 8.
Definition allotrope_element_xenon_z : nat := 54.

Lemma allotrope_carbon_z_is_6 :
  allotrope_element_carbon_z = 6.
Proof. reflexivity. Qed.

Lemma allotrope_phosphorus_z_is_15 :
  allotrope_element_phosphorus_z = 15.
Proof. reflexivity. Qed.

Lemma allotrope_oxygen_z_is_8 :
  allotrope_element_oxygen_z = 8.
Proof. reflexivity. Qed.

Lemma allotrope_xenon_z_is_54 :
  allotrope_element_xenon_z = 54.
Proof. reflexivity. Qed.

Lemma allotrope_c_p_o_z_valid :
  allotrope_element_z_valid allotrope_element_carbon_z = true /\
  allotrope_element_z_valid allotrope_element_phosphorus_z = true /\
  allotrope_element_z_valid allotrope_element_oxygen_z = true.
Proof.
  repeat split;
  unfold allotrope_element_z_valid, iupac_table_cardinality; reflexivity.
Qed.

Definition allotrope_witness_z_not_xe_copy (z : nat) : bool :=
  negb (Nat.eqb z allotrope_element_xenon_z).

Lemma carbon_not_xe_copy :
  allotrope_witness_z_not_xe_copy allotrope_element_carbon_z = true.
Proof. reflexivity. Qed.

Lemma phosphorus_not_xe_copy :
  allotrope_witness_z_not_xe_copy allotrope_element_phosphorus_z = true.
Proof. reflexivity. Qed.

Lemma oxygen_not_xe_copy :
  allotrope_witness_z_not_xe_copy allotrope_element_oxygen_z = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Allotrope geometry variants — same Z, distinct Geometry_n           *)
(* ------------------------------------------------------------------ *)

Inductive carbon_allotrope_kind : Type :=
  | carbon_diamond
  | carbon_graphite
  | carbon_unauthorized.

Inductive phosphorus_allotrope_kind : Type :=
  | phosphorus_white
  | phosphorus_red
  | phosphorus_unauthorized.

Inductive oxygen_allotrope_kind : Type :=
  | oxygen_dioxygen
  | oxygen_ozone
  | oxygen_unauthorized.

Definition carbon_allotrope_kind_beq (k1 k2 : carbon_allotrope_kind) : bool :=
  match k1, k2 with
  | carbon_diamond, carbon_diamond => true
  | carbon_graphite, carbon_graphite => true
  | carbon_unauthorized, carbon_unauthorized => true
  | _, _ => false
  end.

Definition phosphorus_allotrope_kind_beq (k1 k2 : phosphorus_allotrope_kind) : bool :=
  match k1, k2 with
  | phosphorus_white, phosphorus_white => true
  | phosphorus_red, phosphorus_red => true
  | phosphorus_unauthorized, phosphorus_unauthorized => true
  | _, _ => false
  end.

Definition oxygen_allotrope_kind_beq (k1 k2 : oxygen_allotrope_kind) : bool :=
  match k1, k2 with
  | oxygen_dioxygen, oxygen_dioxygen => true
  | oxygen_ozone, oxygen_ozone => true
  | oxygen_unauthorized, oxygen_unauthorized => true
  | _, _ => false
  end.

Record allotrope_binding : Type := {
  allotrope_parent_z : nat
}.

Definition allotropeBindingCarbon : allotrope_binding :=
  {| allotrope_parent_z := allotrope_element_carbon_z |}.

Definition allotropeBindingPhosphorus : allotrope_binding :=
  {| allotrope_parent_z := allotrope_element_phosphorus_z |}.

Definition allotropeBindingOxygen : allotrope_binding :=
  {| allotrope_parent_z := allotrope_element_oxygen_z |}.

Definition allotropeBindingTrivial : allotrope_binding :=
  {| allotrope_parent_z := 0 |}.

Definition allotropeBindingNontrivial (b : allotrope_binding) : bool :=
  Nat.ltb 0 (allotrope_parent_z b).

Lemma allotrope_binding_carbon_nontrivial :
  allotropeBindingNontrivial allotropeBindingCarbon = true.
Proof. reflexivity. Qed.

Lemma allotrope_binding_trivial_not_nontrivial :
  allotropeBindingNontrivial allotropeBindingTrivial = false.
Proof. reflexivity. Qed.

Definition allotropeBindingIdentityConserved (b1 b2 : allotrope_binding) : bool :=
  Nat.eqb (allotrope_parent_z b1) (allotrope_parent_z b2).

Record carbon_allotrope_witness : Type := {
  carbon_allotrope_binding : allotrope_binding;
  carbon_allotrope_kind_tag : carbon_allotrope_kind;
  carbon_allotrope_class_index : nat
}.

Record phosphorus_allotrope_witness : Type := {
  phosphorus_allotrope_binding : allotrope_binding;
  phosphorus_allotrope_kind_tag : phosphorus_allotrope_kind;
  phosphorus_allotrope_class_index : nat
}.

Record oxygen_allotrope_witness : Type := {
  oxygen_allotrope_binding : allotrope_binding;
  oxygen_allotrope_kind_tag : oxygen_allotrope_kind;
  oxygen_allotrope_class_index : nat
}.

Definition carbonAllotropeDiamond : carbon_allotrope_witness :=
  {| carbon_allotrope_binding := allotropeBindingCarbon;
     carbon_allotrope_kind_tag := carbon_diamond;
     carbon_allotrope_class_index := pattern_class_allotrope_idx |}.

Definition carbonAllotropeGraphite : carbon_allotrope_witness :=
  {| carbon_allotrope_binding := allotropeBindingCarbon;
     carbon_allotrope_kind_tag := carbon_graphite;
     carbon_allotrope_class_index := pattern_class_allotrope_idx |}.

Definition phosphorusAllotropeWhite : phosphorus_allotrope_witness :=
  {| phosphorus_allotrope_binding := allotropeBindingPhosphorus;
     phosphorus_allotrope_kind_tag := phosphorus_white;
     phosphorus_allotrope_class_index := pattern_class_allotrope_idx |}.

Definition phosphorusAllotropeRed : phosphorus_allotrope_witness :=
  {| phosphorus_allotrope_binding := allotropeBindingPhosphorus;
     phosphorus_allotrope_kind_tag := phosphorus_red;
     phosphorus_allotrope_class_index := pattern_class_allotrope_idx |}.

Definition oxygenAllotropeO2 : oxygen_allotrope_witness :=
  {| oxygen_allotrope_binding := allotropeBindingOxygen;
     oxygen_allotrope_kind_tag := oxygen_dioxygen;
     oxygen_allotrope_class_index := pattern_class_allotrope_idx |}.

Definition oxygenAllotropeO3 : oxygen_allotrope_witness :=
  {| oxygen_allotrope_binding := allotropeBindingOxygen;
     oxygen_allotrope_kind_tag := oxygen_ozone;
     oxygen_allotrope_class_index := pattern_class_allotrope_idx |}.

Lemma carbon_diamond_graphite_same_z :
  allotropeBindingIdentityConserved
    (carbon_allotrope_binding carbonAllotropeDiamond)
    (carbon_allotrope_binding carbonAllotropeGraphite) = true.
Proof. reflexivity. Qed.

Lemma carbon_diamond_graphite_z_is_6 :
  allotrope_parent_z (carbon_allotrope_binding carbonAllotropeDiamond) = 6 /\
  allotrope_parent_z (carbon_allotrope_binding carbonAllotropeGraphite) = 6.
Proof. repeat split; reflexivity. Qed.

Lemma phosphorus_white_red_same_z :
  allotropeBindingIdentityConserved
    (phosphorus_allotrope_binding phosphorusAllotropeWhite)
    (phosphorus_allotrope_binding phosphorusAllotropeRed) = true.
Proof. reflexivity. Qed.

Lemma oxygen_o2_o3_same_z :
  allotropeBindingIdentityConserved
    (oxygen_allotrope_binding oxygenAllotropeO2)
    (oxygen_allotrope_binding oxygenAllotropeO3) = true.
Proof. reflexivity. Qed.

Definition carbon_allotrope_class_honest (w : carbon_allotrope_witness) : bool :=
  Nat.eqb (carbon_allotrope_class_index w) pattern_class_allotrope_idx &&
  negb (carbon_allotrope_kind_beq (carbon_allotrope_kind_tag w) carbon_unauthorized).

Lemma carbon_diamond_class_honest :
  carbon_allotrope_class_honest carbonAllotropeDiamond = true.
Proof. reflexivity. Qed.

Lemma carbon_graphite_class_honest :
  carbon_allotrope_class_honest carbonAllotropeGraphite = true.
Proof. reflexivity. Qed.

Lemma carbon_diamond_graphite_distinct_kind :
  negb (carbon_allotrope_kind_beq
    (carbon_allotrope_kind_tag carbonAllotropeDiamond)
    (carbon_allotrope_kind_tag carbonAllotropeGraphite)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Concurrent Π_c product — allotrope factor not XOR enum bucket       *)
(* ------------------------------------------------------------------ *)

Inductive allotrope_product_slot : Type :=
  | allotrope_slot_unwired
  | allotrope_slot_absent
  | allotrope_slot_present.

Definition allotrope_slot_is_present (s : allotrope_product_slot) : bool :=
  match s with
  | allotrope_slot_present => true
  | _ => false
  end.

Record allotrope_concurrent_product : Type := {
  product_allotrope_slot : allotrope_product_slot;
  product_catalysis_slot : allotrope_product_slot;
  product_continuum_slot : allotrope_product_slot
}.

Definition allotropeProductCarbonNuance : allotrope_concurrent_product :=
  {| product_allotrope_slot := allotrope_slot_present;
     product_catalysis_slot := allotrope_slot_present;
     product_continuum_slot := allotrope_slot_present |}.

Definition allotrope_product_present_count (p : allotrope_concurrent_product) : nat :=
  (if allotrope_slot_is_present (product_allotrope_slot p) then 1 else 0) +
  (if allotrope_slot_is_present (product_catalysis_slot p) then 1 else 0) +
  (if allotrope_slot_is_present (product_continuum_slot p) then 1 else 0).

Definition allotrope_product_is_concurrent (p : allotrope_concurrent_product) : bool :=
  Nat.leb 2 (allotrope_product_present_count p).

Lemma carbon_nuance_product_present_count_three :
  allotrope_product_present_count allotropeProductCarbonNuance = 3.
Proof. reflexivity. Qed.

Lemma carbon_nuance_product_is_concurrent :
  allotrope_product_is_concurrent allotropeProductCarbonNuance = true.
Proof.
  unfold allotrope_product_is_concurrent.
  rewrite carbon_nuance_product_present_count_three.
  reflexivity.
Qed.

Inductive allotrope_witness_kind : Type :=
  | allotrope_morphism_named
  | xor_enum_bucket_theater.

Definition xor_enum_smuggle (k : allotrope_witness_kind) : bool :=
  match k with
  | xor_enum_bucket_theater => true
  | allotrope_morphism_named => false
  end.

Definition allotropeWitnessXorEnum : allotrope_witness_kind := xor_enum_bucket_theater.
Definition allotropeWitnessNamed : allotrope_witness_kind := allotrope_morphism_named.

Lemma xor_enum_smuggle_true :
  xor_enum_smuggle allotropeWitnessXorEnum = true.
Proof. reflexivity. Qed.

Lemma named_allotrope_not_xor_enum :
  xor_enum_smuggle allotropeWitnessNamed = false.
Proof. reflexivity. Qed.

Definition xorEnumMarker : string := "allotrope_xor_enum_bucket_v1".
Definition productFactorMarker : string := "allotrope_concurrent_product_factor_v1".

Lemma xor_marker_ne_product_factor_marker :
  xorEnumMarker <> productFactorMarker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Not fourth chemistry science / not 26th axiom / not Xe-copy fences  *)
(* ------------------------------------------------------------------ *)

Definition fourthScienceCollisionMarker : string :=
  "Allotrope geometry variants ≠ fourth parallel chemistry science axiom".

Definition twentySixthAxiomCollisionMarker : string :=
  "Allotrope class-10 Π_c product ≠ 26th parallel chemistry axiom".

Definition xeCopyTheaterMarker : string :=
  "Allotrope conservation C/P/O witnesses ≠ Xe Z=54 relativistic continuum copy".

Lemma fourth_science_collision_named :
  fourthScienceCollisionMarker <> "".
Proof. discriminate. Qed.

Lemma twenty_sixth_axiom_collision_named :
  twentySixthAxiomCollisionMarker <> "".
Proof. discriminate. Qed.

Lemma xe_copy_theater_named :
  xeCopyTheaterMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Allotrope bar — Proved-without-bar fail-closed                      *)
(* ------------------------------------------------------------------ *)

Inductive allotrope_bar_presence : Type :=
  | allotrope_bar_absent
  | allotrope_bar_present.

Record allotrope_claim_bar : Type := {
  allotrope_bar_presence_tag : allotrope_bar_presence;
  allotrope_bar_defect_total : nat
}.

Definition allotropeClaimBarAbsent : allotrope_claim_bar :=
  {| allotrope_bar_presence_tag := allotrope_bar_absent;
     allotrope_bar_defect_total := 0 |}.

Definition allotrope_claim_bar_zero_defect (b : allotrope_claim_bar) : bool :=
  match allotrope_bar_presence_tag b with
  | allotrope_bar_absent => false
  | allotrope_bar_present => Nat.eqb (allotrope_bar_defect_total b) 0
  end.

(* ------------------------------------------------------------------ *)
(*  Allotrope **conservation** verdict — fail-closed close lattice       *)
(* ------------------------------------------------------------------ *)

Inductive allotrope_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_allotrope_named_ok
  | verdict_trivial_z_refuse
  | verdict_xor_enum_refuse
  | verdict_xe_copy_refuse
  | verdict_fourth_science_refuse
  | verdict_twenty_sixth_axiom_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition allotrope_conservation_verdict_ok
  (v : allotrope_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_allotrope_named_ok => true
  | _ => false
  end.

Record allotrope_incidence : Type := {
  allotrope_inc_binding : allotrope_binding;
  allotrope_inc_carbon : carbon_allotrope_witness;
  allotrope_inc_witness_kind : allotrope_witness_kind;
  allotrope_inc_level : nat
}.

Definition allotropeIncidenceNontrivial (h : allotrope_incidence) : bool :=
  Nat.ltb 0 (allotrope_inc_level h).

Definition allotropeIncidenceCarbonDiamondL1 : allotrope_incidence :=
  {| allotrope_inc_binding := allotropeBindingCarbon;
     allotrope_inc_carbon := carbonAllotropeDiamond;
     allotrope_inc_witness_kind := allotrope_morphism_named;
     allotrope_inc_level := 1 |}.

Definition allotropeIncidenceCarbonGraphiteL1 : allotrope_incidence :=
  {| allotrope_inc_binding := allotropeBindingCarbon;
     allotrope_inc_carbon := carbonAllotropeGraphite;
     allotrope_inc_witness_kind := allotrope_morphism_named;
     allotrope_inc_level := 1 |}.

Definition allotropeIncidenceTrivial : allotrope_incidence :=
  {| allotrope_inc_binding := allotropeBindingTrivial;
     allotrope_inc_carbon := carbonAllotropeDiamond;
     allotrope_inc_witness_kind := allotrope_morphism_named;
     allotrope_inc_level := 0 |}.

Definition allotropeIncidenceXorEnum : allotrope_incidence :=
  {| allotrope_inc_binding := allotropeBindingCarbon;
     allotrope_inc_carbon := carbonAllotropeDiamond;
     allotrope_inc_witness_kind := xor_enum_bucket_theater;
     allotrope_inc_level := 1 |}.

Definition allotropeIncidenceXeCopy : allotrope_incidence :=
  {| allotrope_inc_binding := {| allotrope_parent_z := allotrope_element_xenon_z |};
     allotrope_inc_carbon := carbonAllotropeDiamond;
     allotrope_inc_witness_kind := allotrope_morphism_named;
     allotrope_inc_level := 1 |}.

Definition evaluate_allotrope_incidence
  (m : AllotropeConservationModality)
  (h : allotrope_incidence)
  (b : allotrope_claim_bar)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_xor_enum : bool)
  (claim_fourth_science : bool)
  (claim_twenty_sixth_axiom : bool)
  (claim_xe_copy : bool) : allotrope_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_fourth_science
            then verdict_fourth_science_refuse
            else if claim_twenty_sixth_axiom
                 then verdict_twenty_sixth_axiom_refuse
                 else if claim_xe_copy
                      then verdict_xe_copy_refuse
                      else if xor_enum_smuggle (allotrope_inc_witness_kind h)
                           then verdict_xor_enum_refuse
                           else if claim_xor_enum
                                then verdict_xor_enum_refuse
                                else if negb (allotropeIncidenceNontrivial h)
                                     then verdict_trivial_z_refuse
                                     else if negb (allotropeBindingNontrivial
                                                     (allotrope_inc_binding h))
                                          then verdict_trivial_z_refuse
                                          else if negb (carbon_allotrope_class_honest
                                                          (allotrope_inc_carbon h))
                                               then verdict_xor_enum_refuse
                                               else if negb (allotrope_witness_z_not_xe_copy
                                                               (allotrope_parent_z
                                                                  (allotrope_inc_binding h)))
                                                    then verdict_xe_copy_refuse
                                                    else
                                                      match m with
                                                      | allotrope_conservation_unwired =>
                                                          verdict_allotrope_named_ok
                                                      | allotrope_conservation_assumed
                                                      | allotrope_conservation_surrogate =>
                                                          verdict_unwired_ok
                                                      | allotrope_conservation_proved =>
                                                          verdict_proved_without_bar_refuse
                                                      end.

Definition evaluate_allotrope_conservation_close
  (m : AllotropeConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : allotrope_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | allotrope_conservation_unwired => verdict_unwired_ok
    | allotrope_conservation_assumed
    | allotrope_conservation_proved
    | allotrope_conservation_surrogate => verdict_allotrope_named_ok
    end.

(* ------------------------------------------------------------------ *)
(*  Allotrope pins — structure witnesses, laws not Proved               *)
(* ------------------------------------------------------------------ *)

Definition allotropeProved : bool := false.

Lemma allotrope_proved_false : allotropeProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

Definition notFourthChemistryScience : bool := true.

Lemma not_fourth_chemistry_science : notFourthChemistryScience = true.
Proof. reflexivity. Qed.

Definition notTwentySixthAxiom : bool := true.

Lemma not_twenty_sixth_axiom : notTwentySixthAxiom = true.
Proof. reflexivity. Qed.

Definition notXeCopyAllotrope : bool := true.

Lemma not_xe_copy_allotrope : notXeCopyAllotrope = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close + named carbon allotrope witnesses                    *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_allotrope_conservation_close
    allotrope_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_allotrope_conservation_close
    allotrope_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma carbon_diamond_named_ok :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonDiamondL1
    allotropeClaimBarAbsent false false false false false false =
  verdict_allotrope_named_ok.
Proof. reflexivity. Qed.

Lemma carbon_graphite_named_ok :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonGraphiteL1
    allotropeClaimBarAbsent false false false false false false =
  verdict_allotrope_named_ok.
Proof. reflexivity. Qed.

Theorem named_carbon_allotrope_conservation :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonDiamondL1
    allotropeClaimBarAbsent false false false false false false =
  verdict_allotrope_named_ok /\
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonGraphiteL1
    allotropeClaimBarAbsent false false false false false false =
  verdict_allotrope_named_ok /\
  allotropeBindingIdentityConserved
    (allotrope_inc_binding allotropeIncidenceCarbonDiamondL1)
    (allotrope_inc_binding allotropeIncidenceCarbonGraphiteL1) = true /\
  negb (carbon_allotrope_kind_beq
    (carbon_allotrope_kind_tag carbonAllotropeDiamond)
    (carbon_allotrope_kind_tag carbonAllotropeGraphite)) = true /\
  allotrope_product_is_concurrent allotropeProductCarbonNuance = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma trivial_z_refused :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceTrivial
    allotropeClaimBarAbsent false false false false false false =
  verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_z_fail_closed :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceTrivial
    allotropeClaimBarAbsent false false false false false false =
  verdict_trivial_z_refuse /\
  allotrope_conservation_verdict_ok
    (evaluate_allotrope_incidence
       allotrope_conservation_unwired allotropeIncidenceTrivial
       allotropeClaimBarAbsent false false false false false false) =
  false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold allotrope_conservation_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

Lemma xor_enum_refused :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceXorEnum
    allotropeClaimBarAbsent false false false false false false =
  verdict_xor_enum_refuse.
Proof. reflexivity. Qed.

Lemma xe_copy_refused :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceXeCopy
    allotropeClaimBarAbsent false false false false false false =
  verdict_xe_copy_refuse.
Proof. reflexivity. Qed.

Theorem xe_copy_fail_closed :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceXeCopy
    allotropeClaimBarAbsent false false false false false false =
  verdict_xe_copy_refuse /\
  allotrope_conservation_verdict_ok
    (evaluate_allotrope_incidence
       allotrope_conservation_unwired allotropeIncidenceXeCopy
       allotropeClaimBarAbsent false false false false false false) =
  false.
Proof.
  split.
  - apply xe_copy_refused.
  - unfold allotrope_conservation_verdict_ok.
    rewrite xe_copy_refused.
    reflexivity.
Qed.

Lemma green_invent_refuse_unwired :
  evaluate_allotrope_conservation_close
    allotrope_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  allotrope_conservation_verdict_ok
    (evaluate_allotrope_conservation_close
       allotrope_conservation_unwired true false) =
  false.
Proof.
  unfold allotrope_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma proved_without_bar_refuse :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonDiamondL1
    allotropeClaimBarAbsent false true false false false false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Lemma production_wired_refuse :
  evaluate_allotrope_conservation_close
    allotrope_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_allotrope_conservation.

Definition allotrope_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition allotropeDoesNotMintFourthScience : bool :=
  notFourthChemistryScience.

Definition allotropeDoesNotClaimProved : bool :=
  negb allotropeProved.

Lemma allotrope_knowing_fiber_ok :
  allotrope_conservation_fiber_ok fiber_quantum_knowing = true.
Proof. reflexivity. Qed.

Lemma allotrope_meso_acting_fiber_not_ok :
  allotrope_conservation_fiber_ok fiber_meso_acting = false.
Proof. reflexivity. Qed.

Theorem allotrope_conservation_routes_knowing_not_meso :
  allotrope_conservation_fiber_ok fiber_quantum_knowing = true /\
  allotrope_conservation_fiber_ok fiber_meso_acting = false /\
  allotropeDoesNotMintFourthScience = true /\
  allotropeDoesNotClaimProved = true /\
  notXeCopyAllotrope = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named allotrope + fail-closed + fiber + class 10 *)
(* ------------------------------------------------------------------ *)

Theorem allotrope_conservation_fixture_scaffold :
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonDiamondL1
    allotropeClaimBarAbsent false false false false false false =
    verdict_allotrope_named_ok /\
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceTrivial
    allotropeClaimBarAbsent false false false false false false =
    verdict_trivial_z_refuse /\
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceXorEnum
    allotropeClaimBarAbsent false false false false false false =
    verdict_xor_enum_refuse /\
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceXeCopy
    allotropeClaimBarAbsent false false false false false false =
    verdict_xe_copy_refuse /\
  evaluate_allotrope_incidence
    allotrope_conservation_unwired allotropeIncidenceCarbonDiamondL1
    allotropeClaimBarAbsent false true false false false false =
    verdict_proved_without_bar_refuse /\
  evaluate_allotrope_conservation_close
    allotrope_conservation_unwired false false =
    verdict_unwired_ok /\
  allotrope_conservation_fiber_ok fiber_quantum_knowing = true /\
  allotrope_conservation_fiber_ok fiber_meso_acting = false /\
  allotropeProved = false /\
  allotropeBindingIdentityConserved
    (carbon_allotrope_binding carbonAllotropeDiamond)
    (carbon_allotrope_binding carbonAllotropeGraphite) = true /\
  allotropeBindingIdentityConserved
    (phosphorus_allotrope_binding phosphorusAllotropeWhite)
    (phosphorus_allotrope_binding phosphorusAllotropeRed) = true /\
  allotropeBindingIdentityConserved
    (oxygen_allotrope_binding oxygenAllotropeO2)
    (oxygen_allotrope_binding oxygenAllotropeO3) = true /\
  allotrope_product_is_concurrent allotropeProductCarbonNuance = true /\
  xorEnumMarker <> productFactorMarker.
Proof.
  repeat split.
  all: try reflexivity.
  apply xor_marker_ne_product_factor_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — allotrope class)     *)
(* ------------------------------------------------------------------ *)

Definition allotropeGeometryAuthority : string :=
  "umst/umst-chem/src/allotrope_geometry_variants.rs".

Definition chemIntCrossAllotropeAuthority : string :=
  "CHEM-INT-CROSS-ALLOTROPE-CONSERVATION".

Definition allotropeConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ALLOTROPE-CONSERVATION".

Definition allotropeConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ALLOTROPE-CONSERVATION pattern class allotrope conservation class 10 concurrent Pi_c product factor not XOR same Z many geometry variants C Z=6 diamond graphite P Z=15 white red O Z=8 O2 O3 ElementId conserved Geometry_n varies not Xe Z=54 copy not fourth chemistry science not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse allotropeProved false Unwired knowing quantum fiber not meso acting one axiom second law conservation not GREEN not physics GREEN not production_wired".

Lemma allotrope_conservation_cell_id :
  allotropeConservationCellId = "CHEM-FORMAL-Q-COQ-ALLOTROPE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma allotrope_conservation_cites_geometry_rs :
  allotropeGeometryAuthority <> "".
Proof. discriminate. Qed.

Lemma allotrope_conservation_cites_int_cross :
  chemIntCrossAllotropeAuthority = "CHEM-INT-CROSS-ALLOTROPE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma allotrope_conservation_cites_x10_row :
  crossClassifierAllotropeRowId = "X10".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**                    *)
(* ------------------------------------------------------------------ *)

Definition allotropeSecondLawConservationFraming : string :=
  "second_law_conservation_allotrope_one_axiom_not_fourth_science_not_26th_axiom_not_xe_copy".

Lemma allotrope_not_fourth_science_axiom :
  allotropeSecondLawConservationFraming <> "fourth_chemistry_science_axiom".
Proof. discriminate. Qed.

Lemma allotrope_not_twenty_sixth_axiom_framing :
  allotropeSecondLawConservationFraming <> "twenty_sixth_chemistry_axiom".
Proof. discriminate. Qed.

Lemma allotrope_not_xe_copy_framing :
  allotropeSecondLawConservationFraming <> "xe_z54_relativistic_continuum_copy".
Proof. discriminate. Qed.

Lemma allotrope_second_law_conservation_framing :
  allotropeSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma allotrope_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma allotrope_conservation_modality_unwired :
  allotropeConservationModalityCurrent = allotrope_conservation_unwired.
Proof. reflexivity. Qed.

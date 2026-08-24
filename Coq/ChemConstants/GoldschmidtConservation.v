(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: GoldschmidtConservation.v                             *)
(*                                                                      *)
(*  Knowing-fiber Coq: Goldschmidt ore-class **conservation**.           *)
(*  Siderophile / lithophile / chalcophile = Ore⊗G⊗fO₂ concurrent       *)
(*  product factor (X5: class 6 ⊗ 7 ⊗ 17) — XOR enum refuse; not a     *)
(*  26th axiom / not fourth chemistry science. Fe Z=26 conserved across  *)
(*  metal/oxide/sulfide assemblages. Cu 29 / Si 14 / He 2 closed-shell  *)
(*  no-ore (missing Interact, not nobility). folklore list refuse;     *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed; trivial    *)
(*  Z=0 refuse. goldschmidtProved false. Modality Unwired.              *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt ore-class **conservation** modality (Unwired / Assumed / *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive GoldschmidtConservationModality : Type :=
  | goldschmidt_conservation_unwired
  | goldschmidt_conservation_assumed
  | goldschmidt_conservation_proved
  | goldschmidt_conservation_surrogate.

Definition goldschmidtConservationModalityCurrent : GoldschmidtConservationModality :=
  goldschmidt_conservation_unwired.

Definition goldschmidt_modality_lattice_cardinality : nat := 4.

Lemma goldschmidt_modality_lattice_cardinality_is_four :
  goldschmidt_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma goldschmidt_modality_lattice_not_118_squared :
  negb (Nat.eqb goldschmidt_modality_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold goldschmidt_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — element **conservation** scaffold (not 118² table)   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition goldschmidt_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

Definition goldschmidt_element_iron_z : nat := 26.
Definition goldschmidt_element_copper_z : nat := 29.
Definition goldschmidt_element_silicon_z : nat := 14.
Definition goldschmidt_element_helium_z : nat := 2.
Definition goldschmidt_element_oganesson_z : nat := 118.

Lemma goldschmidt_iron_z_is_26 :
  goldschmidt_element_iron_z = 26.
Proof. reflexivity. Qed.

Lemma goldschmidt_copper_z_is_29 :
  goldschmidt_element_copper_z = 29.
Proof. reflexivity. Qed.

Lemma goldschmidt_silicon_z_is_14 :
  goldschmidt_element_silicon_z = 14.
Proof. reflexivity. Qed.

Lemma goldschmidt_helium_z_is_2 :
  goldschmidt_element_helium_z = 2.
Proof. reflexivity. Qed.

Lemma goldschmidt_oganesson_z_is_118 :
  goldschmidt_element_oganesson_z = 118.
Proof. reflexivity. Qed.

Lemma goldschmidt_fe_cu_z_valid :
  goldschmidt_element_z_valid goldschmidt_element_iron_z = true /\
  goldschmidt_element_z_valid goldschmidt_element_copper_z = true.
Proof.
  split; unfold goldschmidt_element_z_valid, goldschmidt_element_iron_z,
    goldschmidt_element_copper_z, iupac_table_cardinality; reflexivity.
Qed.

Lemma goldschmidt_si_he_z_valid :
  goldschmidt_element_z_valid goldschmidt_element_silicon_z = true /\
  goldschmidt_element_z_valid goldschmidt_element_helium_z = true.
Proof.
  split; unfold goldschmidt_element_z_valid, goldschmidt_element_silicon_z,
    goldschmidt_element_helium_z, iupac_table_cardinality; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pattern taxonomy X5 — class 6 ⊗ 7 ⊗ 17 concurrent product           *)
(* ------------------------------------------------------------------ *)

Definition pattern_class_6_ore_idx : nat := 6.
Definition pattern_class_7_g_stability_idx : nat := 7.
Definition pattern_class_17_fo2_idx : nat := 17.

Lemma pattern_class_6_is_six :
  pattern_class_6_ore_idx = 6.
Proof. reflexivity. Qed.

Lemma pattern_class_7_is_seven :
  pattern_class_7_g_stability_idx = 7.
Proof. reflexivity. Qed.

Lemma pattern_class_17_is_seventeen :
  pattern_class_17_fo2_idx = 17.
Proof. reflexivity. Qed.

Definition goldschmidt_x5_product_factor_count : nat := 3.

Lemma goldschmidt_x5_concurrent_product :
  goldschmidt_x5_product_factor_count = 3.
Proof. reflexivity. Qed.

Lemma goldschmidt_x5_not_xor_enum :
  negb (Nat.eqb goldschmidt_x5_product_factor_count 1) = true.
Proof. reflexivity. Qed.

Definition crossClassifierX5RowId : string := "X5".

Lemma cross_classifier_x5_row_named :
  crossClassifierX5RowId = "X5".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Ore assemblage kinds — Fe Z identity across metal/oxide/sulfide     *)
(* ------------------------------------------------------------------ *)

Inductive ore_assemblage_kind : Type :=
  | assemblage_metal
  | assemblage_oxide
  | assemblage_sulfide
  | assemblage_unauthorized.

Definition ore_assemblage_kind_beq (k1 k2 : ore_assemblage_kind) : bool :=
  match k1, k2 with
  | assemblage_metal, assemblage_metal => true
  | assemblage_oxide, assemblage_oxide => true
  | assemblage_sulfide, assemblage_sulfide => true
  | assemblage_unauthorized, assemblage_unauthorized => true
  | _, _ => false
  end.

Record goldschmidt_binding : Type := {
  goldschmidt_parent_z : nat
}.

Definition goldschmidtBindingFe : goldschmidt_binding :=
  {| goldschmidt_parent_z := goldschmidt_element_iron_z |}.

Definition goldschmidtBindingCu : goldschmidt_binding :=
  {| goldschmidt_parent_z := goldschmidt_element_copper_z |}.

Definition goldschmidtBindingSi : goldschmidt_binding :=
  {| goldschmidt_parent_z := goldschmidt_element_silicon_z |}.

Definition goldschmidtBindingHe : goldschmidt_binding :=
  {| goldschmidt_parent_z := goldschmidt_element_helium_z |}.

Definition goldschmidtBindingTrivial : goldschmidt_binding :=
  {| goldschmidt_parent_z := 0 |}.

Definition goldschmidtBindingNontrivial (b : goldschmidt_binding) : bool :=
  Nat.ltb 0 (goldschmidt_parent_z b).

Lemma goldschmidt_binding_fe_nontrivial :
  goldschmidtBindingNontrivial goldschmidtBindingFe = true.
Proof. reflexivity. Qed.

Lemma goldschmidt_binding_trivial_not_nontrivial :
  goldschmidtBindingNontrivial goldschmidtBindingTrivial = false.
Proof. reflexivity. Qed.

Definition goldschmidtBindingIdentityConserved (b1 b2 : goldschmidt_binding) : bool :=
  Nat.eqb (goldschmidt_parent_z b1) (goldschmidt_parent_z b2).

Record ore_assemblage_witness : Type := {
  ore_assemblage_binding : goldschmidt_binding;
  ore_assemblage_kind_tag : ore_assemblage_kind;
  ore_assemblage_class_index : nat
}.

Definition oreAssemblageFeMetal : ore_assemblage_witness :=
  {| ore_assemblage_binding := goldschmidtBindingFe;
     ore_assemblage_kind_tag := assemblage_metal;
     ore_assemblage_class_index := pattern_class_6_ore_idx |}.

Definition oreAssemblageFeOxide : ore_assemblage_witness :=
  {| ore_assemblage_binding := goldschmidtBindingFe;
     ore_assemblage_kind_tag := assemblage_oxide;
     ore_assemblage_class_index := pattern_class_6_ore_idx |}.

Definition oreAssemblageFeSulfide : ore_assemblage_witness :=
  {| ore_assemblage_binding := goldschmidtBindingFe;
     ore_assemblage_kind_tag := assemblage_sulfide;
     ore_assemblage_class_index := pattern_class_6_ore_idx |}.

Lemma fe_metal_oxide_sulfide_same_z :
  goldschmidtBindingIdentityConserved
    (ore_assemblage_binding oreAssemblageFeMetal)
    (ore_assemblage_binding oreAssemblageFeOxide) = true /\
  goldschmidtBindingIdentityConserved
    (ore_assemblage_binding oreAssemblageFeMetal)
    (ore_assemblage_binding oreAssemblageFeSulfide) = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma fe_metal_oxide_sulfide_z_is_26 :
  goldschmidt_parent_z (ore_assemblage_binding oreAssemblageFeMetal) = 26 /\
  goldschmidt_parent_z (ore_assemblage_binding oreAssemblageFeOxide) = 26 /\
  goldschmidt_parent_z (ore_assemblage_binding oreAssemblageFeSulfide) = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  G-stability and fO₂ ladder witnesses — class 7 and 17             *)
(* ------------------------------------------------------------------ *)

Record g_stability_witness : Type := {
  g_stability_tag : string;
  g_stability_class_index : nat
}.

Record fo2_ladder_witness : Type := {
  fo2_ladder_tag : string;
  fo2_ladder_class_index : nat
}.

Definition gStabilityCoreGMin : g_stability_witness :=
  {| g_stability_tag := "core_g_min_partition";
     g_stability_class_index := pattern_class_7_g_stability_idx |}.

Definition gStabilityCrustGMin : g_stability_witness :=
  {| g_stability_tag := "crust_oxide_g_min_hull";
     g_stability_class_index := pattern_class_7_g_stability_idx |}.

Definition gStabilitySulfideGMin : g_stability_witness :=
  {| g_stability_tag := "sulfide_g_min_partition";
     g_stability_class_index := pattern_class_7_g_stability_idx |}.

Definition fo2LadderCoreLow : fo2_ladder_witness :=
  {| fo2_ladder_tag := "core_low_fo2_ladder";
     fo2_ladder_class_index := pattern_class_17_fo2_idx |}.

Definition fo2LadderCrust : fo2_ladder_witness :=
  {| fo2_ladder_tag := "crust_intermediate_fo2_ladder";
     fo2_ladder_class_index := pattern_class_17_fo2_idx |}.

Definition g_stability_class_honest (g : g_stability_witness) : bool :=
  Nat.eqb (g_stability_class_index g) pattern_class_7_g_stability_idx.

Definition fo2_ladder_class_honest (f : fo2_ladder_witness) : bool :=
  Nat.eqb (fo2_ladder_class_index f) pattern_class_17_fo2_idx.

Lemma g_stability_core_honest :
  g_stability_class_honest gStabilityCoreGMin = true.
Proof. reflexivity. Qed.

Lemma fo2_ladder_core_honest :
  fo2_ladder_class_honest fo2LadderCoreLow = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt Ore⊗G⊗fO₂ product factor — concurrent, not XOR enum    *)
(* ------------------------------------------------------------------ *)

Record goldschmidt_ore_product_factor : Type := {
  product_ore : ore_assemblage_witness;
  product_g_stability : g_stability_witness;
  product_fo2_ladder : fo2_ladder_witness
}.

Definition goldschmidtProductSiderophile : goldschmidt_ore_product_factor :=
  {| product_ore := oreAssemblageFeMetal;
     product_g_stability := gStabilityCoreGMin;
     product_fo2_ladder := fo2LadderCoreLow |}.

Definition goldschmidtProductLithophile : goldschmidt_ore_product_factor :=
  {| product_ore := oreAssemblageFeOxide;
     product_g_stability := gStabilityCrustGMin;
     product_fo2_ladder := fo2LadderCrust |}.

Definition goldschmidtProductChalcophile : goldschmidt_ore_product_factor :=
  {| product_ore := oreAssemblageFeSulfide;
     product_g_stability := gStabilitySulfideGMin;
     product_fo2_ladder := fo2LadderCrust |}.

Definition goldschmidt_product_factor_honest (p : goldschmidt_ore_product_factor) : bool :=
  Nat.eqb (ore_assemblage_class_index (product_ore p)) pattern_class_6_ore_idx &&
  g_stability_class_honest (product_g_stability p) &&
  fo2_ladder_class_honest (product_fo2_ladder p).

Lemma siderophile_product_honest :
  goldschmidt_product_factor_honest goldschmidtProductSiderophile = true.
Proof. reflexivity. Qed.

Lemma lithophile_product_honest :
  goldschmidt_product_factor_honest goldschmidtProductLithophile = true.
Proof. reflexivity. Qed.

Lemma chalcophile_product_honest :
  goldschmidt_product_factor_honest goldschmidtProductChalcophile = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Affinity tags — derived from product factor, not XOR enum bucket   *)
(* ------------------------------------------------------------------ *)

Inductive goldschmidt_affinity_tag : Type :=
  | affinity_siderophile
  | affinity_lithophile
  | affinity_chalcophile
  | affinity_xor_enum_bucket.

Definition goldschmidt_affinity_tag_beq (t1 t2 : goldschmidt_affinity_tag) : bool :=
  match t1, t2 with
  | affinity_siderophile, affinity_siderophile => true
  | affinity_lithophile, affinity_lithophile => true
  | affinity_chalcophile, affinity_chalcophile => true
  | affinity_xor_enum_bucket, affinity_xor_enum_bucket => true
  | _, _ => false
  end.

Record goldschmidt_affinity_witness : Type := {
  affinity_tag : goldschmidt_affinity_tag;
  affinity_product : goldschmidt_ore_product_factor
}.

Definition goldschmidtAffinitySiderophile : goldschmidt_affinity_witness :=
  {| affinity_tag := affinity_siderophile;
     affinity_product := goldschmidtProductSiderophile |}.

Definition goldschmidtAffinityLithophile : goldschmidt_affinity_witness :=
  {| affinity_tag := affinity_lithophile;
     affinity_product := goldschmidtProductLithophile |}.

Definition goldschmidtAffinityChalcophile : goldschmidt_affinity_witness :=
  {| affinity_tag := affinity_chalcophile;
     affinity_product := goldschmidtProductChalcophile |}.

Definition goldschmidtAffinityXorEnum : goldschmidt_affinity_witness :=
  {| affinity_tag := affinity_xor_enum_bucket;
     affinity_product := goldschmidtProductSiderophile |}.

Definition goldschmidt_affinity_derived_from_product (w : goldschmidt_affinity_witness) : bool :=
  goldschmidt_product_factor_honest (affinity_product w) &&
  negb (goldschmidt_affinity_tag_beq (affinity_tag w) affinity_xor_enum_bucket).

Lemma siderophile_affinity_derived :
  goldschmidt_affinity_derived_from_product goldschmidtAffinitySiderophile = true.
Proof. reflexivity. Qed.

Lemma lithophile_affinity_derived :
  goldschmidt_affinity_derived_from_product goldschmidtAffinityLithophile = true.
Proof. reflexivity. Qed.

Lemma chalcophile_affinity_derived :
  goldschmidt_affinity_derived_from_product goldschmidtAffinityChalcophile = true.
Proof. reflexivity. Qed.

Lemma xor_enum_affinity_not_derived :
  goldschmidt_affinity_derived_from_product goldschmidtAffinityXorEnum = false.
Proof. reflexivity. Qed.

Definition goldschmidtAffinitiesConcurrentProduct : bool :=
  goldschmidt_affinity_derived_from_product goldschmidtAffinitySiderophile &&
  goldschmidt_affinity_derived_from_product goldschmidtAffinityLithophile &&
  goldschmidt_affinity_derived_from_product goldschmidtAffinityChalcophile.

Lemma goldschmidt_affinities_concurrent_product_true :
  goldschmidtAffinitiesConcurrentProduct = true.
Proof.
  unfold goldschmidtAffinitiesConcurrentProduct.
  simpl.
  repeat split; reflexivity.
Qed.

Definition xorEnumMarker : string := "goldschmidt_xor_enum_bucket_v1".
Definition productFactorMarker : string := "goldschmidt_ore_product_factor_v1".

Lemma xor_marker_ne_product_factor_marker :
  xorEnumMarker <> productFactorMarker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Closed-shell no-ore — Cu/Si/He missing Interact, not nobility       *)
(* ------------------------------------------------------------------ *)

Inductive closed_shell_no_ore_reason : Type :=
  | no_ore_missing_interact
  | no_ore_nobility_theater.

Definition closed_shell_no_ore_honest (r : closed_shell_no_ore_reason) : bool :=
  match r with
  | no_ore_missing_interact => true
  | no_ore_nobility_theater => false
  end.

Record closed_shell_no_ore_witness : Type := {
  no_ore_binding : goldschmidt_binding;
  no_ore_reason_tag : closed_shell_no_ore_reason;
  no_ore_has_interact_witness : bool
}.

Definition closedShellNoOreCu : closed_shell_no_ore_witness :=
  {| no_ore_binding := goldschmidtBindingCu;
     no_ore_reason_tag := no_ore_missing_interact;
     no_ore_has_interact_witness := false |}.

Definition closedShellNoOreSi : closed_shell_no_ore_witness :=
  {| no_ore_binding := goldschmidtBindingSi;
     no_ore_reason_tag := no_ore_missing_interact;
     no_ore_has_interact_witness := false |}.

Definition closedShellNoOreHe : closed_shell_no_ore_witness :=
  {| no_ore_binding := goldschmidtBindingHe;
     no_ore_reason_tag := no_ore_missing_interact;
     no_ore_has_interact_witness := false |}.

Definition closed_shell_no_ore_valid (w : closed_shell_no_ore_witness) : bool :=
  closed_shell_no_ore_honest (no_ore_reason_tag w) &&
  negb (no_ore_has_interact_witness w).

Lemma closed_shell_cu_no_ore_valid :
  closed_shell_no_ore_valid closedShellNoOreCu = true.
Proof. reflexivity. Qed.

Lemma closed_shell_si_no_ore_valid :
  closed_shell_no_ore_valid closedShellNoOreSi = true.
Proof. reflexivity. Qed.

Lemma closed_shell_he_no_ore_valid :
  closed_shell_no_ore_valid closedShellNoOreHe = true.
Proof. reflexivity. Qed.

Lemma closed_shell_cu_z_is_29 :
  goldschmidt_parent_z (no_ore_binding closedShellNoOreCu) = 29.
Proof. reflexivity. Qed.

Lemma closed_shell_si_z_is_14 :
  goldschmidt_parent_z (no_ore_binding closedShellNoOreSi) = 14.
Proof. reflexivity. Qed.

Lemma closed_shell_he_z_is_2 :
  goldschmidt_parent_z (no_ore_binding closedShellNoOreHe) = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Folklore list vs monoidal Ore morphism — refuse smuggle             *)
(* ------------------------------------------------------------------ *)

Inductive ore_witness_kind : Type :=
  | ore_morphism_named
  | folklore_list_theater.

Definition folklore_list_smuggle (k : ore_witness_kind) : bool :=
  match k with
  | folklore_list_theater => true
  | ore_morphism_named => false
  end.

Definition oreWitnessMonoidalNamed : ore_witness_kind := ore_morphism_named.
Definition oreWitnessFolkloreList : ore_witness_kind := folklore_list_theater.

Lemma folklore_list_smuggle_true :
  folklore_list_smuggle oreWitnessFolkloreList = true.
Proof. reflexivity. Qed.

Lemma monoidal_ore_not_folklore :
  folklore_list_smuggle oreWitnessMonoidalNamed = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not fourth chemistry science / not 26th axiom collision fences      *)
(* ------------------------------------------------------------------ *)

Definition fourthScienceCollisionMarker : string :=
  "Goldschmidt affinity classes ≠ fourth parallel chemistry science axiom".

Definition twentySixthAxiomCollisionMarker : string :=
  "Goldschmidt Ore⊗G⊗fO₂ product ≠ 26th parallel chemistry axiom".

Lemma fourth_science_collision_named :
  fourthScienceCollisionMarker <> "".
Proof. discriminate. Qed.

Lemma twenty_sixth_axiom_collision_named :
  twentySixthAxiomCollisionMarker <> "".
Proof. discriminate. Qed.

Definition claimFourthScience (claim : bool) : bool := claim.
Definition claimTwentySixthAxiom (claim : bool) : bool := claim.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt bar — Proved-without-bar fail-closed                    *)
(* ------------------------------------------------------------------ *)

Inductive goldschmidt_bar_presence : Type :=
  | goldschmidt_bar_absent
  | goldschmidt_bar_present.

Record goldschmidt_claim_bar : Type := {
  goldschmidt_bar_presence_tag : goldschmidt_bar_presence;
  goldschmidt_bar_defect_total : nat
}.

Definition goldschmidtClaimBarAbsent : goldschmidt_claim_bar :=
  {| goldschmidt_bar_presence_tag := goldschmidt_bar_absent;
     goldschmidt_bar_defect_total := 0 |}.

Definition goldschmidtClaimBarZeroDefect : goldschmidt_claim_bar :=
  {| goldschmidt_bar_presence_tag := goldschmidt_bar_present;
     goldschmidt_bar_defect_total := 0 |}.

Definition goldschmidt_claim_bar_zero_defect (b : goldschmidt_claim_bar) : bool :=
  match goldschmidt_bar_presence_tag b with
  | goldschmidt_bar_absent => false
  | goldschmidt_bar_present => Nat.eqb (goldschmidt_bar_defect_total b) 0
  end.

Lemma goldschmidt_claim_bar_zero_defect_true :
  goldschmidt_claim_bar_zero_defect goldschmidtClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma goldschmidt_claim_bar_absent_not_zero_defect :
  goldschmidt_claim_bar_zero_defect goldschmidtClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt **conservation** verdict — fail-closed close lattice    *)
(* ------------------------------------------------------------------ *)

Inductive goldschmidt_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_goldschmidt_named_ok
  | verdict_trivial_z_refuse
  | verdict_xor_enum_refuse
  | verdict_folklore_list_refuse
  | verdict_fourth_science_refuse
  | verdict_twenty_sixth_axiom_refuse
  | verdict_closed_shell_nobility_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition goldschmidt_conservation_verdict_ok
  (v : goldschmidt_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_goldschmidt_named_ok => true
  | _ => false
  end.

Definition goldschmidt_conservation_verdict_beq
  (v1 v2 : goldschmidt_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_goldschmidt_named_ok, verdict_goldschmidt_named_ok => true
  | verdict_trivial_z_refuse, verdict_trivial_z_refuse => true
  | verdict_xor_enum_refuse, verdict_xor_enum_refuse => true
  | verdict_folklore_list_refuse, verdict_folklore_list_refuse => true
  | verdict_fourth_science_refuse, verdict_fourth_science_refuse => true
  | verdict_twenty_sixth_axiom_refuse, verdict_twenty_sixth_axiom_refuse => true
  | verdict_closed_shell_nobility_refuse, verdict_closed_shell_nobility_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | verdict_proved_without_bar_refuse, verdict_proved_without_bar_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Record goldschmidt_incidence : Type := {
  goldschmidt_inc_binding : goldschmidt_binding;
  goldschmidt_inc_affinity : goldschmidt_affinity_witness;
  goldschmidt_inc_ore_witness_kind : ore_witness_kind;
  goldschmidt_inc_level : nat
}.

Definition goldschmidtIncidenceNontrivial (h : goldschmidt_incidence) : bool :=
  Nat.ltb 0 (goldschmidt_inc_level h).

Definition goldschmidtIncidenceFeSiderophileL1 : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingFe;
     goldschmidt_inc_affinity := goldschmidtAffinitySiderophile;
     goldschmidt_inc_ore_witness_kind := ore_morphism_named;
     goldschmidt_inc_level := 1 |}.

Definition goldschmidtIncidenceFeLithophileL1 : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingFe;
     goldschmidt_inc_affinity := goldschmidtAffinityLithophile;
     goldschmidt_inc_ore_witness_kind := ore_morphism_named;
     goldschmidt_inc_level := 1 |}.

Definition goldschmidtIncidenceFeChalcophileL1 : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingFe;
     goldschmidt_inc_affinity := goldschmidtAffinityChalcophile;
     goldschmidt_inc_ore_witness_kind := ore_morphism_named;
     goldschmidt_inc_level := 1 |}.

Definition goldschmidtIncidenceTrivial : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingTrivial;
     goldschmidt_inc_affinity := goldschmidtAffinitySiderophile;
     goldschmidt_inc_ore_witness_kind := ore_morphism_named;
     goldschmidt_inc_level := 0 |}.

Definition goldschmidtIncidenceXorEnum : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingFe;
     goldschmidt_inc_affinity := goldschmidtAffinityXorEnum;
     goldschmidt_inc_ore_witness_kind := ore_morphism_named;
     goldschmidt_inc_level := 1 |}.

Definition goldschmidtIncidenceFolkloreList : goldschmidt_incidence :=
  {| goldschmidt_inc_binding := goldschmidtBindingFe;
     goldschmidt_inc_affinity := goldschmidtAffinitySiderophile;
     goldschmidt_inc_ore_witness_kind := folklore_list_theater;
     goldschmidt_inc_level := 1 |}.

Definition evaluate_goldschmidt_incidence
  (m : GoldschmidtConservationModality)
  (h : goldschmidt_incidence)
  (b : goldschmidt_claim_bar)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_xor_enum : bool)
  (claim_fourth_science : bool)
  (claim_twenty_sixth_axiom : bool) : goldschmidt_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_fourth_science
            then verdict_fourth_science_refuse
            else if claim_twenty_sixth_axiom
                 then verdict_twenty_sixth_axiom_refuse
                 else if folklore_list_smuggle (goldschmidt_inc_ore_witness_kind h)
                      then verdict_folklore_list_refuse
                      else if claim_xor_enum
                           then verdict_xor_enum_refuse
                           else if negb (goldschmidt_affinity_derived_from_product
                                           (goldschmidt_inc_affinity h))
                                then verdict_xor_enum_refuse
                                else if negb (goldschmidtIncidenceNontrivial h)
                                     then verdict_trivial_z_refuse
                                     else if negb (goldschmidtBindingNontrivial
                                                     (goldschmidt_inc_binding h))
                                          then verdict_trivial_z_refuse
                                          else
                                            match m with
                                            | goldschmidt_conservation_unwired =>
                                                verdict_goldschmidt_named_ok
                                            | goldschmidt_conservation_assumed
                                            | goldschmidt_conservation_surrogate =>
                                                verdict_unwired_ok
                                            | goldschmidt_conservation_proved =>
                                                verdict_proved_without_bar_refuse
                                            end.

Definition evaluate_goldschmidt_conservation_close
  (m : GoldschmidtConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : goldschmidt_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | goldschmidt_conservation_unwired => verdict_unwired_ok
    | goldschmidt_conservation_assumed
    | goldschmidt_conservation_proved
    | goldschmidt_conservation_surrogate => verdict_goldschmidt_named_ok
    end.

Definition goldschmidt_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_goldschmidt_conservation_close
          goldschmidt_conservation_proved claim_physics_green claim_production_wired with
  | verdict_goldschmidt_named_ok => true
  | _ => false
  end.

Definition evaluate_closed_shell_no_ore
  (w : closed_shell_no_ore_witness) : goldschmidt_conservation_verdict :=
  if closed_shell_no_ore_valid w
  then verdict_goldschmidt_named_ok
  else verdict_closed_shell_nobility_refuse.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt **conservation** law cells — four laws, open @ Unwired   *)
(* ------------------------------------------------------------------ *)

Inductive goldschmidt_conservation_law : Type :=
  | law_goldschmidt_product_named
  | law_xor_enum_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition goldschmidt_conservation_law_count : nat := 4.

Lemma goldschmidt_conservation_law_count_is_four :
  goldschmidt_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive goldschmidt_conservation_law_witness : Type :=
  | goldschmidt_law_witness_open
  | goldschmidt_law_witness_proved.

Definition evaluate_goldschmidt_conservation_law_witness
  (law : goldschmidt_conservation_law) (m : GoldschmidtConservationModality)
  : goldschmidt_conservation_law_witness :=
  match m with
  | goldschmidt_conservation_unwired
  | goldschmidt_conservation_assumed
  | goldschmidt_conservation_surrogate => goldschmidt_law_witness_open
  | goldschmidt_conservation_proved => goldschmidt_law_witness_proved
  end.

Lemma all_goldschmidt_conservation_laws_open_at_unwired :
  evaluate_goldschmidt_conservation_law_witness law_goldschmidt_product_named
    goldschmidt_conservation_unwired = goldschmidt_law_witness_open /\
  evaluate_goldschmidt_conservation_law_witness law_xor_enum_refuse
    goldschmidt_conservation_unwired = goldschmidt_law_witness_open /\
  evaluate_goldschmidt_conservation_law_witness law_green_invent_refuse
    goldschmidt_conservation_unwired = goldschmidt_law_witness_open /\
  evaluate_goldschmidt_conservation_law_witness law_production_wired_refuse
    goldschmidt_conservation_unwired = goldschmidt_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Goldschmidt pins (structure witnesses — laws not Proved)          *)
(* ------------------------------------------------------------------ *)

Definition goldschmidtProved : bool := false.

Lemma goldschmidt_proved_false : goldschmidtProved = false.
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

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_unwired false false) =
  true.
Proof.
  unfold goldschmidt_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe siderophile / lithophile / chalcophile close — Z conserved   *)
(* ------------------------------------------------------------------ *)

Lemma goldschmidt_fe_siderophile_named_ok :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false false false false =
  verdict_goldschmidt_named_ok.
Proof. reflexivity. Qed.

Lemma goldschmidt_fe_lithophile_named_ok :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeLithophileL1
    goldschmidtClaimBarAbsent false false false false false =
  verdict_goldschmidt_named_ok.
Proof. reflexivity. Qed.

Lemma goldschmidt_fe_chalcophile_named_ok :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeChalcophileL1
    goldschmidtClaimBarAbsent false false false false false =
  verdict_goldschmidt_named_ok.
Proof. reflexivity. Qed.

Theorem named_goldschmidt_ore_class_conservation :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false false false false =
  verdict_goldschmidt_named_ok /\
  goldschmidtBindingIdentityConserved
    (goldschmidt_inc_binding goldschmidtIncidenceFeSiderophileL1)
    (goldschmidt_inc_binding goldschmidtIncidenceFeLithophileL1) = true /\
  goldschmidt_product_factor_honest
    (affinity_product (goldschmidt_inc_affinity goldschmidtIncidenceFeSiderophileL1)) = true /\
  goldschmidtAffinitiesConcurrentProduct = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma goldschmidt_named_close_ok :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_proved false false =
  verdict_goldschmidt_named_ok.
Proof. reflexivity. Qed.

Theorem named_goldschmidt_conservation_close :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_proved false false =
  verdict_goldschmidt_named_ok /\
  goldschmidt_conservation_authorized false false = true.
Proof.
  split.
  - apply goldschmidt_named_close_ok.
  - unfold goldschmidt_conservation_authorized.
    rewrite goldschmidt_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial Z=0 fail-closed — **conservation** refuse                   *)
(* ------------------------------------------------------------------ *)

Lemma trivial_z_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceTrivial
    goldschmidtClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_z_fail_closed :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceTrivial
    goldschmidtClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse /\
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_incidence
       goldschmidt_conservation_unwired goldschmidtIncidenceTrivial
       goldschmidtClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold goldschmidt_conservation_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR enum fail-closed — Ore⊗G⊗fO₂ product refuse XOR bucket          *)
(* ------------------------------------------------------------------ *)

Lemma xor_enum_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceXorEnum
    goldschmidtClaimBarAbsent false false false false false =
  verdict_xor_enum_refuse.
Proof. reflexivity. Qed.

Theorem xor_enum_fail_closed :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceXorEnum
    goldschmidtClaimBarAbsent false false false false false =
  verdict_xor_enum_refuse /\
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_incidence
       goldschmidt_conservation_unwired goldschmidtIncidenceXorEnum
       goldschmidtClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply xor_enum_refused.
  - unfold goldschmidt_conservation_verdict_ok.
    rewrite xor_enum_refused.
    reflexivity.
Qed.

Lemma xor_enum_claim_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false true false false =
  verdict_xor_enum_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Folklore list fail-closed                                           *)
(* ------------------------------------------------------------------ *)

Lemma folklore_list_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFolkloreList
    goldschmidtClaimBarAbsent false false false false false =
  verdict_folklore_list_refuse.
Proof. reflexivity. Qed.

Theorem folklore_list_fail_closed :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFolkloreList
    goldschmidtClaimBarAbsent false false false false false =
  verdict_folklore_list_refuse /\
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_incidence
       goldschmidt_conservation_unwired goldschmidtIncidenceFolkloreList
       goldschmidtClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply folklore_list_refused.
  - unfold goldschmidt_conservation_verdict_ok.
    rewrite folklore_list_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fourth science / 26th axiom smuggle refuse                            *)
(* ------------------------------------------------------------------ *)

Lemma fourth_science_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false false true false =
  verdict_fourth_science_refuse.
Proof. reflexivity. Qed.

Lemma twenty_sixth_axiom_refused :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false false false true =
  verdict_twenty_sixth_axiom_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_unwired true false) =
  false.
Proof.
  unfold goldschmidt_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_goldschmidt_incidence_refuse :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent true false false false false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — **conservation** refuse            *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false true false false false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false true false false false =
  verdict_proved_without_bar_refuse /\
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_incidence
       goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
       goldschmidtClaimBarAbsent false true false false false) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold goldschmidt_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — Goldschmidt not production wired          *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  goldschmidt_conservation_verdict_ok
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_proved false true) =
  false.
Proof.
  unfold goldschmidt_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Closed-shell no-ore witnesses — Cu/Si/He missing Interact           *)
(* ------------------------------------------------------------------ *)

Theorem closed_shell_no_ore_cu_si_he :
  evaluate_closed_shell_no_ore closedShellNoOreCu =
    verdict_goldschmidt_named_ok /\
  evaluate_closed_shell_no_ore closedShellNoOreSi =
    verdict_goldschmidt_named_ok /\
  evaluate_closed_shell_no_ore closedShellNoOreHe =
    verdict_goldschmidt_named_ok /\
  goldschmidt_parent_z (no_ore_binding closedShellNoOreCu) = 29 /\
  goldschmidt_parent_z (no_ore_binding closedShellNoOreSi) = 14 /\
  goldschmidt_parent_z (no_ore_binding closedShellNoOreHe) = 2.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  **Goldschmidt** **conservation** coherence scaffold                  *)
(* ------------------------------------------------------------------ *)

Definition goldschmidt_conservation_coherence_scaffold : bool :=
  goldschmidt_conservation_verdict_beq
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_proved false false)
    verdict_goldschmidt_named_ok &&
  goldschmidt_conservation_verdict_beq
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_unwired true false)
    verdict_green_invent_refuse &&
  goldschmidt_conservation_verdict_beq
    (evaluate_goldschmidt_conservation_close
       goldschmidt_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma goldschmidt_conservation_coherence_scaffold_true :
  goldschmidt_conservation_coherence_scaffold = true.
Proof.
  unfold goldschmidt_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Acting fiber routing — meso/acting not knowing/quantum              *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_goldschmidt_conservation.

Definition goldschmidt_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_meso_acting => true
  | fiber_quantum_knowing => false
  end.

Definition goldschmidtDoesNotMintFourthScience : bool :=
  notFourthChemistryScience.

Definition goldschmidtDoesNotClaimProved : bool :=
  negb goldschmidtProved.

Lemma goldschmidt_meso_acting_fiber_ok :
  goldschmidt_conservation_fiber_ok fiber_meso_acting = true.
Proof. reflexivity. Qed.

Lemma goldschmidt_knowing_fiber_not_ok :
  goldschmidt_conservation_fiber_ok fiber_quantum_knowing = false.
Proof. reflexivity. Qed.

Theorem goldschmidt_conservation_routes_meso_not_knowing :
  goldschmidt_conservation_fiber_ok fiber_meso_acting = true /\
  goldschmidt_conservation_fiber_ok fiber_quantum_knowing = false /\
  goldschmidtDoesNotMintFourthScience = true /\
  goldschmidtDoesNotClaimProved = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named Goldschmidt + fail-closed + fiber + X5     *)
(* ------------------------------------------------------------------ *)

Theorem goldschmidt_conservation_fixture_scaffold :
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false false false false false =
    verdict_goldschmidt_named_ok /\
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceTrivial
    goldschmidtClaimBarAbsent false false false false false =
    verdict_trivial_z_refuse /\
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceXorEnum
    goldschmidtClaimBarAbsent false false false false false =
    verdict_xor_enum_refuse /\
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFolkloreList
    goldschmidtClaimBarAbsent false false false false false =
    verdict_folklore_list_refuse /\
  evaluate_goldschmidt_incidence
    goldschmidt_conservation_unwired goldschmidtIncidenceFeSiderophileL1
    goldschmidtClaimBarAbsent false true false false false =
    verdict_proved_without_bar_refuse /\
  evaluate_goldschmidt_conservation_close
    goldschmidt_conservation_unwired false false =
    verdict_unwired_ok /\
  goldschmidt_conservation_fiber_ok fiber_meso_acting = true /\
  goldschmidt_conservation_fiber_ok fiber_quantum_knowing = false /\
  goldschmidtProved = false /\
  goldschmidtAffinitiesConcurrentProduct = true /\
  xorEnumMarker <> productFactorMarker.
Proof.
  repeat split.
  all: try reflexivity.
  apply xor_marker_ne_product_factor_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — Goldschmidt ore)     *)
(* ------------------------------------------------------------------ *)

Definition goldschmidtOreAuthority : string :=
  "umst/umst-chem/src/x_rows/goldschmidt_ore.rs".

Definition chemIntCrossGoldschmidtOreAuthority : string :=
  "CHEM-INT-CROSS-GOLDSCHMIDT-ORE".

Definition goldschmidtConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-GOLDSCHMIDT-CONSERVATION".

Definition goldschmidtConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-GOLDSCHMIDT-CONSERVATION Goldschmidt ore-class conservation siderophile lithophile chalcophile Ore⊗G⊗fO₂ concurrent product factor X5 class 6⊗7⊗17 XOR enum refuse not fourth chemistry science not 26th axiom Fe Z=26 metal oxide sulfide identity conserved Cu 29 Si 14 He 2 closed-shell no-ore missing Interact not nobility folklore list refuse GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse goldschmidtProved false Unwired acting fiber meso not knowing one axiom second law conservation not GREEN not physics GREEN not production_wired".

Lemma goldschmidt_conservation_cell_id :
  goldschmidtConservationCellId = "CHEM-FORMAL-Q-COQ-GOLDSCHMIDT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma goldschmidt_conservation_cites_goldschmidt_ore_rs :
  goldschmidtOreAuthority <> "".
Proof. discriminate. Qed.

Lemma goldschmidt_conservation_cites_int_cross :
  chemIntCrossGoldschmidtOreAuthority = "CHEM-INT-CROSS-GOLDSCHMIDT-ORE".
Proof. reflexivity. Qed.

Lemma goldschmidt_conservation_cites_x5_row :
  crossClassifierX5RowId = "X5".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**                    *)
(* ------------------------------------------------------------------ *)

Definition goldschmidtSecondLawConservationFraming : string :=
  "second_law_conservation_goldschmidt_one_axiom_not_fourth_science_not_26th_axiom".

Lemma goldschmidt_not_fourth_science_axiom :
  goldschmidtSecondLawConservationFraming <> "fourth_chemistry_science_axiom".
Proof. discriminate. Qed.

Lemma goldschmidt_not_twenty_sixth_axiom_framing :
  goldschmidtSecondLawConservationFraming <> "twenty_sixth_chemistry_axiom".
Proof. discriminate. Qed.

Lemma goldschmidt_second_law_conservation_framing :
  goldschmidtSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma goldschmidt_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma goldschmidt_conservation_modality_unwired :
  goldschmidtConservationModalityCurrent = goldschmidt_conservation_unwired.
Proof. reflexivity. Qed.

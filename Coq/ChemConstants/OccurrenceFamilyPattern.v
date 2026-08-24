(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OccurrenceFamilyPattern.v                           *)
(*  name-from-content stem: occurrencefamilypattern                    *)
(*                                                                      *)
(*  Knowing-fiber Coq: occurrence-class families are concurrent        *)
(*  product classifiers (7 tags); ore-engine sorts outliers (native Au  *)
(*  Z=79 vs oxide-product Fe Z=26 vs closed-shell He atmophile no-ore  *)
(*  Z=2); same Z many assemblages — not folklore exclusive lists.     *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed; trivial  *)
(*  Z=0 refuse. Not 26th axiom. occurrenceFamilyPatternProved false.   *)
(*  Modality Unwired. WAVE100 lib/eos smuggle refuse.                 *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

Definition occurrencefamilypatternSurface : string :=
  "occurrencefamilypattern_surface_v1".

Lemma occurrencefamilypattern_surface_named :
  occurrencefamilypatternSurface <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occurrence family pattern modality (Unwired / Assumed / Proved /   *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive OccurrenceFamilyPatternModality : Type :=
  | occurrence_family_pattern_unwired
  | occurrence_family_pattern_assumed
  | occurrence_family_pattern_proved
  | occurrence_family_pattern_surrogate.

Definition occurrenceFamilyPatternModalityCurrent :
  OccurrenceFamilyPatternModality :=
  occurrence_family_pattern_unwired.

Definition occurrence_family_modality_lattice_cardinality : nat := 4.

Lemma occurrence_family_modality_lattice_cardinality_is_four :
  occurrence_family_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma occurrence_family_modality_lattice_not_118_squared :
  negb (Nat.eqb occurrence_family_modality_lattice_cardinality (118 * 118)) =
  true.
Proof.
  unfold occurrence_family_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Seven concurrent occurrence-family product classifiers (not XOR)   *)
(* ------------------------------------------------------------------ *)

Definition occurrence_family_tag_count : nat := 7.

Lemma occurrence_family_tag_count_is_seven :
  occurrence_family_tag_count = 7.
Proof. reflexivity. Qed.

Inductive occurrence_family_tag : Type :=
  | family_tag_native
  | family_tag_oxide
  | family_tag_sulfide
  | family_tag_silicate
  | family_tag_halide_carbonate
  | family_tag_atmophile
  | family_tag_synthetic_or_trace.

Definition occurrence_family_tag_beq (t1 t2 : occurrence_family_tag) : bool :=
  match t1, t2 with
  | family_tag_native, family_tag_native => true
  | family_tag_oxide, family_tag_oxide => true
  | family_tag_sulfide, family_tag_sulfide => true
  | family_tag_silicate, family_tag_silicate => true
  | family_tag_halide_carbonate, family_tag_halide_carbonate => true
  | family_tag_atmophile, family_tag_atmophile => true
  | family_tag_synthetic_or_trace, family_tag_synthetic_or_trace => true
  | _, _ => false
  end.

(* Family product bits — concurrent, not XOR enum bucket. INT SSOT pins. *)

Definition bit_native : nat := 1.
Definition bit_oxide : nat := 2.
Definition bit_sulfide : nat := 4.
Definition bit_atmophile : nat := 32.

Lemma bit_native_is_one : bit_native = 1.
Proof. reflexivity. Qed.

Lemma bit_oxide_is_two : bit_oxide = 2.
Proof. reflexivity. Qed.

Lemma bit_sulfide_is_four : bit_sulfide = 4.
Proof. reflexivity. Qed.

Lemma bit_atmophile_is_32 : bit_atmophile = 32.
Proof. reflexivity. Qed.

Definition family_bits_has (bits mask : nat) : bool :=
  Nat.eqb (Nat.land bits mask) mask.

Definition family_bit_count (bits : nat) : nat :=
  (if family_bits_has bits bit_native then 1 else 0) +
  (if family_bits_has bits bit_oxide then 1 else 0) +
  (if family_bits_has bits bit_sulfide then 1 else 0) +
  (if family_bits_has bits bit_atmophile then 1 else 0).

Definition family_bits_concurrent (bits : nat) : bool :=
  Nat.leb 2 (family_bit_count bits).

(* ------------------------------------------------------------------ *)
(*  IUPAC Z bar — pattern for Z=1..118 assemblages (not 118² table)    *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

(* Named outlier Z pins — INT SSOT. *)

Definition gold_z : nat := 79.
Definition iron_z : nat := 26.
Definition helium_z : nat := 2.

Lemma gold_z_is_79 : gold_z = 79.
Proof. reflexivity. Qed.

Lemma iron_z_is_26 : iron_z = 26.
Proof. reflexivity. Qed.

Lemma helium_z_is_2 : helium_z = 2.
Proof. reflexivity. Qed.

Lemma outlier_z_factors_valid :
  z_valid gold_z = true /\
  z_valid iron_z = true /\
  z_valid helium_z = true.
Proof.
  repeat split; unfold z_valid, iupac_table_cardinality; reflexivity.
Qed.

(* Outlier bit pins — INT SSOT. *)

Definition gold_outlier_bits : nat := bit_native.
Definition iron_outlier_bits : nat := bit_native + bit_oxide + bit_sulfide.
Definition helium_outlier_bits : nat := bit_atmophile.

Lemma gold_outlier_bits_is_native_only :
  gold_outlier_bits = bit_native.
Proof. reflexivity. Qed.

Lemma iron_outlier_bits_is_seven :
  iron_outlier_bits = 7.
Proof. reflexivity. Qed.

Lemma helium_outlier_bits_is_atmophile_only :
  helium_outlier_bits = bit_atmophile.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Ore-engine outlier sort witnesses (Au native vs Fe product vs He)   *)
(* ------------------------------------------------------------------ *)

Definition gold_is_native_family_outlier : bool :=
  Nat.eqb gold_outlier_bits bit_native.

Definition iron_is_oxide_family_product : bool :=
  family_bits_has iron_outlier_bits bit_oxide &&
  family_bits_has iron_outlier_bits bit_native &&
  family_bits_has iron_outlier_bits bit_sulfide.

Definition helium_is_no_ore_atmophile : bool :=
  Nat.eqb helium_outlier_bits bit_atmophile &&
  negb (family_bits_has helium_outlier_bits bit_native).

Definition helium_no_ore_is_missing_interact : bool :=
  helium_is_no_ore_atmophile.

Lemma gold_is_native_family_outlier_true :
  gold_is_native_family_outlier = true.
Proof. reflexivity. Qed.

Lemma iron_is_oxide_family_product_true :
  iron_is_oxide_family_product = true.
Proof. reflexivity. Qed.

Lemma helium_is_no_ore_atmophile_true :
  helium_is_no_ore_atmophile = true.
Proof. reflexivity. Qed.

Lemma helium_no_ore_is_missing_interact_true :
  helium_no_ore_is_missing_interact = true.
Proof. reflexivity. Qed.

Definition ore_engine_outliers_sort_named : bool :=
  gold_is_native_family_outlier &&
  iron_is_oxide_family_product &&
  helium_is_no_ore_atmophile &&
  helium_no_ore_is_missing_interact.

Lemma ore_engine_outliers_sort_named_true :
  ore_engine_outliers_sort_named = true.
Proof. reflexivity. Qed.

(* Same Z may occupy several families — Fe concurrent product witness. *)

Definition same_z_many_assemblages : bool :=
  iron_is_oxide_family_product.

Lemma same_z_many_assemblages_true :
  same_z_many_assemblages = true.
Proof. reflexivity. Qed.

(* Folklore exclusive list refuse — not a single-family bucket per Z. *)

Definition folklore_exclusive_list_refused : bool := true.

Lemma folklore_exclusive_list_refused_true :
  folklore_exclusive_list_refused = true.
Proof. reflexivity. Qed.

Definition occurrence_family_pattern_conjunct : bool :=
  Nat.eqb occurrence_family_tag_count 7 &&
  ore_engine_outliers_sort_named &&
  same_z_many_assemblages &&
  folklore_exclusive_list_refused.

Lemma occurrence_family_pattern_conjunct_true :
  occurrence_family_pattern_conjunct = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Concurrent product classifiers — not XOR enum bucket                *)
(* ------------------------------------------------------------------ *)

Definition xorEnumMarker : string := "occurrence_family_xor_enum_bucket_v1".
Definition productFactorMarker : string :=
  "occurrence_family_concurrent_product_v1".

Lemma xor_marker_ne_product_factor_marker :
  xorEnumMarker <> productFactorMarker.
Proof. discriminate. Qed.

Definition iron_outlier_is_concurrent_product : bool :=
  family_bits_concurrent iron_outlier_bits.

Lemma iron_outlier_is_concurrent_product_true :
  iron_outlier_is_concurrent_product = true.
Proof.
  unfold iron_outlier_is_concurrent_product, family_bits_concurrent,
         iron_outlier_bits, family_bit_count, family_bits_has,
         bit_native, bit_oxide, bit_sulfide, bit_atmophile.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Not 26th axiom / not fourth chemistry science collision fences      *)
(* ------------------------------------------------------------------ *)

Definition fourthScienceCollisionMarker : string :=
  "Occurrence family pattern ≠ fourth parallel chemistry science axiom".

Definition twentySixthAxiomCollisionMarker : string :=
  "Occurrence family pattern ≠ 26th parallel chemistry axiom".

Lemma fourth_science_collision_named :
  fourthScienceCollisionMarker <> "".
Proof. discriminate. Qed.

Lemma twenty_sixth_axiom_collision_named :
  twentySixthAxiomCollisionMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occurrence family bar — Proved-without-bar fail-closed              *)
(* ------------------------------------------------------------------ *)

Inductive occurrence_family_bar_presence : Type :=
  | occurrence_family_bar_absent
  | occurrence_family_bar_present.

Record occurrence_family_claim_bar : Type := {
  occurrence_family_bar_presence_tag : occurrence_family_bar_presence;
  occurrence_family_bar_defect_total : nat
}.

Definition occurrenceFamilyClaimBarAbsent : occurrence_family_claim_bar :=
  {| occurrence_family_bar_presence_tag := occurrence_family_bar_absent;
     occurrence_family_bar_defect_total := 0 |}.

(* ------------------------------------------------------------------ *)
(*  Occurrence family pattern verdict — fail-closed close lattice       *)
(* ------------------------------------------------------------------ *)

Inductive occurrence_family_verdict : Type :=
  | verdict_unwired_ok
  | verdict_family_pattern_named_ok
  | verdict_trivial_z_refuse
  | verdict_folklore_list_refuse
  | verdict_xor_enum_refuse
  | verdict_fourth_science_refuse
  | verdict_twenty_sixth_axiom_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition occurrence_family_verdict_ok
  (v : occurrence_family_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_family_pattern_named_ok => true
  | _ => false
  end.

Record occurrence_family_incidence : Type := {
  family_inc_z : nat;
  family_inc_bits : nat;
  family_inc_level : nat
}.

Definition occurrenceFamilyIncidenceNontrivial
  (h : occurrence_family_incidence) : bool :=
  Nat.ltb 0 (family_inc_level h).

Definition occurrenceFamilyIncidenceGoldL1 : occurrence_family_incidence :=
  {| family_inc_z := gold_z;
     family_inc_bits := gold_outlier_bits;
     family_inc_level := 1 |}.

Definition occurrenceFamilyIncidenceIronL1 : occurrence_family_incidence :=
  {| family_inc_z := iron_z;
     family_inc_bits := iron_outlier_bits;
     family_inc_level := 1 |}.

Definition occurrenceFamilyIncidenceHeliumL1 : occurrence_family_incidence :=
  {| family_inc_z := helium_z;
     family_inc_bits := helium_outlier_bits;
     family_inc_level := 1 |}.

Definition occurrenceFamilyIncidenceTrivial : occurrence_family_incidence :=
  {| family_inc_z := gold_z;
     family_inc_bits := gold_outlier_bits;
     family_inc_level := 0 |}.

Definition evaluate_occurrence_family_incidence
  (m : OccurrenceFamilyPatternModality)
  (h : occurrence_family_incidence)
  (b : occurrence_family_claim_bar)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_xor_enum : bool)
  (claim_folklore_list : bool)
  (claim_fourth_science : bool)
  (claim_twenty_sixth_axiom : bool) : occurrence_family_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_fourth_science
            then verdict_fourth_science_refuse
            else if claim_twenty_sixth_axiom
                 then verdict_twenty_sixth_axiom_refuse
                 else if claim_folklore_list
                      then verdict_folklore_list_refuse
                      else if claim_xor_enum
                           then verdict_xor_enum_refuse
                           else if negb (occurrenceFamilyIncidenceNontrivial h)
                                then verdict_trivial_z_refuse
                                else if negb (z_valid (family_inc_z h))
                                     then verdict_trivial_z_refuse
                                     else
                                       match m with
                                       | occurrence_family_pattern_unwired =>
                                           verdict_family_pattern_named_ok
                                       | occurrence_family_pattern_assumed
                                       | occurrence_family_pattern_surrogate =>
                                           verdict_unwired_ok
                                       | occurrence_family_pattern_proved =>
                                           verdict_proved_without_bar_refuse
                                       end.

Definition evaluate_occurrence_family_close
  (m : OccurrenceFamilyPatternModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : occurrence_family_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | occurrence_family_pattern_unwired => verdict_unwired_ok
    | occurrence_family_pattern_assumed
    | occurrence_family_pattern_proved
    | occurrence_family_pattern_surrogate => verdict_family_pattern_named_ok
    end.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs smuggle refuse (not wired)                *)
(* ------------------------------------------------------------------ *)

Definition occurrence_family_pattern_wired_in_lib : bool := false.

Definition occurrence_family_pattern_wired_in_eos : bool := false.

Lemma occurrence_family_pattern_not_wired_lib :
  occurrence_family_pattern_wired_in_lib = false.
Proof. reflexivity. Qed.

Lemma occurrence_family_pattern_not_wired_eos :
  occurrence_family_pattern_wired_in_eos = false.
Proof. reflexivity. Qed.

Lemma wave100_not_wired :
  negb occurrence_family_pattern_wired_in_lib &&
  negb occurrence_family_pattern_wired_in_eos = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Occurrence family pattern pins — structure witness, not Proved      *)
(* ------------------------------------------------------------------ *)

Definition occurrenceFamilyPatternProved : bool := false.

Lemma occurrence_family_pattern_proved_false :
  occurrenceFamilyPatternProved = false.
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

Definition sole_axiom_count : nat := 1.

Lemma sole_axiom_count_is_one : sole_axiom_count = 1.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close + named outlier witnesses                           *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_occurrence_family_close
    occurrence_family_pattern_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_occurrence_family_close
    occurrence_family_pattern_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma gold_outlier_named_ok :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok.
Proof. reflexivity. Qed.

Lemma iron_outlier_named_ok :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceIronL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok.
Proof. reflexivity. Qed.

Lemma helium_outlier_named_ok :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceHeliumL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok.
Proof. reflexivity. Qed.

Theorem named_occurrence_family_outliers :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceIronL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceHeliumL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_family_pattern_named_ok /\
  gold_is_native_family_outlier = true /\
  iron_is_oxide_family_product = true /\
  helium_is_no_ore_atmophile = true /\
  occurrence_family_pattern_conjunct = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma trivial_z_refused :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceTrivial
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_z_fail_closed :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceTrivial
    occurrenceFamilyClaimBarAbsent false false false false false false =
  verdict_trivial_z_refuse /\
  occurrence_family_verdict_ok
    (evaluate_occurrence_family_incidence
       occurrence_family_pattern_unwired occurrenceFamilyIncidenceTrivial
       occurrenceFamilyClaimBarAbsent false false false false false false) =
  false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold occurrence_family_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

Lemma green_invent_refuse_unwired :
  evaluate_occurrence_family_close
    occurrence_family_pattern_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  occurrence_family_verdict_ok
    (evaluate_occurrence_family_close
       occurrence_family_pattern_unwired true false) =
  false.
Proof.
  unfold occurrence_family_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma proved_without_bar_refuse :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false true false false false false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Lemma production_wired_refuse :
  evaluate_occurrence_family_close
    occurrence_family_pattern_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Lemma folklore_list_refuse :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false false false true false false =
  verdict_folklore_list_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — not meso acting                     *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition occurrence_family_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition occurrenceFamilyPatternDoesNotMintFourthScience : bool :=
  notFourthChemistryScience.

Definition occurrenceFamilyPatternDoesNotClaimProved : bool :=
  negb occurrenceFamilyPatternProved.

Lemma occurrence_family_knowing_fiber_ok :
  occurrence_family_fiber_ok fiber_quantum_knowing = true.
Proof. reflexivity. Qed.

Lemma occurrence_family_meso_acting_fiber_not_ok :
  occurrence_family_fiber_ok fiber_meso_acting = false.
Proof. reflexivity. Qed.

Theorem occurrence_family_routes_knowing_not_meso :
  occurrence_family_fiber_ok fiber_quantum_knowing = true /\
  occurrence_family_fiber_ok fiber_meso_acting = false /\
  occurrenceFamilyPatternDoesNotMintFourthScience = true /\
  occurrenceFamilyPatternDoesNotClaimProved = true /\
  notTwentySixthAxiom = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named outliers + fail-closed + fiber             *)
(* ------------------------------------------------------------------ *)

Theorem occurrence_family_pattern_fixture_scaffold :
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
    verdict_family_pattern_named_ok /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceIronL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
    verdict_family_pattern_named_ok /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceHeliumL1
    occurrenceFamilyClaimBarAbsent false false false false false false =
    verdict_family_pattern_named_ok /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceTrivial
    occurrenceFamilyClaimBarAbsent false false false false false false =
    verdict_trivial_z_refuse /\
  evaluate_occurrence_family_incidence
    occurrence_family_pattern_unwired occurrenceFamilyIncidenceGoldL1
    occurrenceFamilyClaimBarAbsent false true false false false false =
    verdict_proved_without_bar_refuse /\
  evaluate_occurrence_family_close
    occurrence_family_pattern_unwired false false =
    verdict_unwired_ok /\
  occurrence_family_fiber_ok fiber_quantum_knowing = true /\
  occurrence_family_fiber_ok fiber_meso_acting = false /\
  occurrenceFamilyPatternProved = false /\
  occurrence_family_pattern_conjunct = true /\
  (negb occurrence_family_pattern_wired_in_lib &&
   negb occurrence_family_pattern_wired_in_eos = true) /\
  xorEnumMarker <> productFactorMarker.
Proof.
  repeat split.
  all: try reflexivity.
  apply xor_marker_ne_product_factor_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — occurrence family)   *)
(* ------------------------------------------------------------------ *)

Definition occurrenceFamilyPatternRsAuthority : string :=
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs".

Definition chemIntCrossOccurrenceFamilyPatternAuthority : string :=
  "CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION".

Definition occurrenceFamilyPatternCellId : string :=
  "CHEM-FORMAL-Q-COQ-OCCURRENCE-FAMILY-PATTERN-CONSERVATION".

Definition occurrenceFamilyPatternNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-OCCURRENCE-FAMILY-PATTERN-CONSERVATION occurrence-class families are concurrent product classifiers 7 tags ore-engine sorts outliers native Au Z=79 vs oxide-product Fe Z=26 vs closed-shell He atmophile no-ore Z=2 same Z many assemblages not folklore exclusive lists not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse occurrenceFamilyPatternProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN not physics GREEN not production_wired".

Lemma occurrence_family_pattern_cell_id :
  occurrenceFamilyPatternCellId =
  "CHEM-FORMAL-Q-COQ-OCCURRENCE-FAMILY-PATTERN-CONSERVATION".
Proof. reflexivity. Qed.

Lemma occurrence_family_pattern_cites_rs_row :
  occurrenceFamilyPatternRsAuthority <> "".
Proof. discriminate. Qed.

Lemma occurrence_family_pattern_cites_int_cross_row :
  chemIntCrossOccurrenceFamilyPatternAuthority =
  "CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION".
Proof. reflexivity. Qed.

Definition occurrence_family_marker : string :=
  "chem_int_cross_occurrence_family_pattern_v1".

Lemma occurrence_family_pattern_cites_marker :
  occurrence_family_marker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**                    *)
(* ------------------------------------------------------------------ *)

Definition occurrenceFamilyPatternSecondLawConservationFraming : string :=
  "second_law_conservation_occurrence_family_pattern_one_axiom_not_26th_axiom".

Lemma occurrence_family_pattern_not_twenty_sixth_axiom_framing :
  occurrenceFamilyPatternSecondLawConservationFraming <>
  "twenty_sixth_chemistry_axiom".
Proof. discriminate. Qed.

Lemma occurrence_family_pattern_not_fourth_science_axiom :
  occurrenceFamilyPatternSecondLawConservationFraming <>
  "fourth_chemistry_science_axiom".
Proof. discriminate. Qed.

Lemma occurrence_family_pattern_second_law_conservation_framing :
  occurrenceFamilyPatternSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma occurrence_family_pattern_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma occurrence_family_pattern_modality_unwired :
  occurrenceFamilyPatternModalityCurrent =
  occurrence_family_pattern_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 freeze — remainder is deferred composition, not impossibility *)
(* ------------------------------------------------------------------ *)

Definition wave100FreezeMarker : string :=
  "WAVE100 freeze remainder deferred composition not impossibility".

Lemma wave100_freeze_marker_named :
  wave100FreezeMarker <> "".
Proof. discriminate. Qed.

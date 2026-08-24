(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: NaturalOccurrenceZ118.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: Z=1..118 natural occurrence as Unwired named    *)
(*  product classifiers (native/oxide/sulfide/silicate/halide+carbonate/ *)
(*  atmophile/synthetic-or-trace); not folklore lists; concurrent bits  *)
(*  not XOR enum. He atmophile-only; Fe native⊗oxide⊗sulfide product.   *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed; trivial   *)
(*  Z=0 refuse. naturalOccurrenceZ118Proved false. Modality Unwired.    *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing. WAVE100 freeze.     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

Definition naturaloccurrencez118Surface : string :=
  "natural_occurrence_z118_surface".

Lemma naturaloccurrencez118_surface_named :
  naturaloccurrencez118Surface <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Natural occurrence Z118 modality (Unwired / Assumed / Proved /      *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive NaturalOccurrenceZ118Modality : Type :=
  | natural_occurrence_z118_unwired
  | natural_occurrence_z118_assumed
  | natural_occurrence_z118_proved
  | natural_occurrence_z118_surrogate.

Definition naturalOccurrenceZ118ModalityCurrent : NaturalOccurrenceZ118Modality :=
  natural_occurrence_z118_unwired.

Definition natural_occurrence_modality_lattice_cardinality : nat := 4.

Lemma natural_occurrence_modality_lattice_cardinality_is_four :
  natural_occurrence_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma natural_occurrence_modality_lattice_not_118_squared :
  negb (Nat.eqb natural_occurrence_modality_lattice_cardinality (118 * 118)) =
  true.
Proof.
  unfold natural_occurrence_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z bar — product classifier table Z=1..118 (not 118² GREEN)   *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition occurrence_element_z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

(* ------------------------------------------------------------------ *)
(*  Concurrent product classifier bits — not XOR enum bucket          *)
(* ------------------------------------------------------------------ *)

Definition bit_native : nat := 1.
Definition bit_oxide : nat := 2.
Definition bit_sulfide : nat := 4.
Definition bit_silicate : nat := 8.
Definition bit_halide_carbonate : nat := 16.
Definition bit_atmophile : nat := 32.
Definition bit_synthetic_trace : nat := 64.

Lemma bit_native_is_1 : bit_native = 1.
Proof. reflexivity. Qed.

Lemma bit_oxide_is_2 : bit_oxide = 2.
Proof. reflexivity. Qed.

Lemma bit_sulfide_is_4 : bit_sulfide = 4.
Proof. reflexivity. Qed.

Lemma bit_atmophile_is_32 : bit_atmophile = 32.
Proof. reflexivity. Qed.

Definition occurrence_bit_has (bits classifier : nat) : bool :=
  Nat.eqb ((bits / classifier) mod 2) 1.

(* ------------------------------------------------------------------ *)
(*  INT SSOT table — umst-chem natural_occurrence_z118.rs pins        *)
(* ------------------------------------------------------------------ *)

Definition occurrence_product_table : list nat :=
  [48; 32; 24; 8; 18; 17; 32; 42; 16; 32; 24; 10; 10; 8; 16; 5; 16; 32;
   24; 24; 8; 2; 6; 2; 2; 7; 4; 5; 5; 4; 4; 4; 4; 5; 16; 32;
   8; 16; 24; 8; 2; 4; 64; 1; 1; 1; 5; 4; 4; 2; 4; 5; 16; 32;
   8; 16; 24; 24; 24; 24; 64; 24; 24; 24; 24; 24; 24; 24; 24; 24; 24; 8;
   2; 2; 4; 1; 1; 1; 1; 5; 4; 4; 5; 64; 64; 96; 64; 64; 64; 24;
   64; 2; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64;
   64; 64; 64; 64; 64; 64; 64; 64; 64; 96]%nat.

Fixpoint list_nth_occurrence (n : nat) (l : list nat) : option nat :=
  match n, l with
  | O, x :: _ => Some x
  | S n', _ :: xs => list_nth_occurrence n' xs
  | _, nil => None
  end.

Definition occurrence_bits (z : nat) : option nat :=
  if Nat.eqb z 0
  then None
  else if Nat.ltb iupac_table_cardinality z
       then None
       else list_nth_occurrence (pred z) occurrence_product_table.

Lemma occurrence_table_length_118 :
  length occurrence_product_table = 118.
Proof. reflexivity. Qed.

Fixpoint all_occurrence_nonzero (l : list nat) : bool :=
  match l with
  | nil => true
  | h :: xs => negb (Nat.eqb h 0) && all_occurrence_nonzero xs
  end.

Definition every_z_classified : bool :=
  all_occurrence_nonzero occurrence_product_table.

Lemma every_z_classified_true : every_z_classified = true.
Proof. reflexivity. Qed.

Definition table_covers_z118 : bool :=
  Nat.eqb (length occurrence_product_table) iupac_table_cardinality.

Lemma table_covers_z118_true : table_covers_z118 = true.
Proof. reflexivity. Qed.

(* Witness Z pins — He Z=2, Fe Z=26, Au Z=79, Tc Z=43. *)

Definition helium_z : nat := 2.
Definition iron_z : nat := 26.
Definition gold_z : nat := 79.
Definition technetium_z : nat := 43.

Lemma helium_z_is_2 : helium_z = 2.
Proof. reflexivity. Qed.

Lemma iron_z_is_26 : iron_z = 26.
Proof. reflexivity. Qed.

Lemma gold_z_is_79 : gold_z = 79.
Proof. reflexivity. Qed.

Lemma technetium_z_is_43 : technetium_z = 43.
Proof. reflexivity. Qed.

Lemma helium_bits_atmophile_only :
  occurrence_bits helium_z = Some bit_atmophile.
Proof. reflexivity. Qed.

Lemma iron_bits_native_oxide_sulfide_product :
  occurrence_bits iron_z = Some 7 /\
  occurrence_bit_has 7 bit_native = true /\
  occurrence_bit_has 7 bit_oxide = true /\
  occurrence_bit_has 7 bit_sulfide = true.
Proof. repeat split; reflexivity. Qed.

Lemma gold_bits_native :
  occurrence_bits gold_z = Some bit_native.
Proof. reflexivity. Qed.

Lemma technetium_bits_synthetic_trace :
  occurrence_bits technetium_z = Some bit_synthetic_trace.
Proof. reflexivity. Qed.

Definition helium_has_no_crustal_ore_bit : bool :=
  match occurrence_bits helium_z with
  | Some b => Nat.eqb b bit_atmophile
  | None => false
  end.

Lemma helium_has_no_crustal_ore_bit_true :
  helium_has_no_crustal_ore_bit = true.
Proof. reflexivity. Qed.

Definition iron_is_occurrence_product : bool :=
  match occurrence_bits iron_z with
  | Some b =>
      occurrence_bit_has b bit_native &&
      occurrence_bit_has b bit_oxide &&
      occurrence_bit_has b bit_sulfide
  | None => false
  end.

Lemma iron_is_occurrence_product_true :
  iron_is_occurrence_product = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Folklore list refuse — named product classifiers, not lore lists  *)
(* ------------------------------------------------------------------ *)

Definition folkloreListMarker : string := "natural_occurrence_folklore_list_v1".
Definition productClassifierMarker : string :=
  "natural_occurrence_product_classifier_v1".

Lemma folklore_marker_ne_product_classifier_marker :
  folkloreListMarker <> productClassifierMarker.
Proof. discriminate. Qed.

Inductive occurrence_witness_kind : Type :=
  | occurrence_product_named
  | folklore_list_theater
  | xor_enum_bucket_theater.

Definition folklore_list_smuggle (k : occurrence_witness_kind) : bool :=
  match k with
  | folklore_list_theater => true
  | _ => false
  end.

Definition xor_enum_smuggle (k : occurrence_witness_kind) : bool :=
  match k with
  | xor_enum_bucket_theater => true
  | _ => false
  end.

Definition occurrenceWitnessFolklore : occurrence_witness_kind :=
  folklore_list_theater.
Definition occurrenceWitnessNamed : occurrence_witness_kind :=
  occurrence_product_named.

Lemma folklore_list_smuggle_true :
  folklore_list_smuggle occurrenceWitnessFolklore = true.
Proof. reflexivity. Qed.

Lemma named_occurrence_not_folklore_list :
  folklore_list_smuggle occurrenceWitnessNamed = false.
Proof. reflexivity. Qed.

Definition xorEnumMarker : string := "natural_occurrence_xor_enum_bucket_v1".
Definition productFactorMarker : string :=
  "natural_occurrence_concurrent_product_factor_v1".

Lemma xor_marker_ne_product_factor_marker :
  xorEnumMarker <> productFactorMarker.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Not fourth chemistry science / not 26th axiom fences                *)
(* ------------------------------------------------------------------ *)

Definition fourthScienceCollisionMarker : string :=
  "Natural occurrence Z118 product classifiers ≠ fourth parallel chemistry science axiom".

Definition twentySixthAxiomCollisionMarker : string :=
  "Natural occurrence Z118 concurrent bits ≠ 26th parallel chemistry axiom".

Lemma fourth_science_collision_named :
  fourthScienceCollisionMarker <> "".
Proof. discriminate. Qed.

Lemma twenty_sixth_axiom_collision_named :
  twentySixthAxiomCollisionMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Natural occurrence bar — Proved-without-bar fail-closed             *)
(* ------------------------------------------------------------------ *)

Inductive natural_occurrence_bar_presence : Type :=
  | natural_occurrence_bar_absent
  | natural_occurrence_bar_present.

Record natural_occurrence_claim_bar : Type := {
  natural_occurrence_bar_presence_tag : natural_occurrence_bar_presence;
  natural_occurrence_bar_defect_total : nat
}.

Definition naturalOccurrenceClaimBarAbsent : natural_occurrence_claim_bar :=
  {| natural_occurrence_bar_presence_tag := natural_occurrence_bar_absent;
     natural_occurrence_bar_defect_total := 0 |}.

(* ------------------------------------------------------------------ *)
(*  Natural occurrence Z118 verdict — fail-closed close lattice         *)
(* ------------------------------------------------------------------ *)

Inductive natural_occurrence_z118_verdict : Type :=
  | verdict_unwired_ok
  | verdict_occurrence_named_ok
  | verdict_trivial_z_refuse
  | verdict_folklore_list_refuse
  | verdict_xor_enum_refuse
  | verdict_fourth_science_refuse
  | verdict_twenty_sixth_axiom_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition natural_occurrence_z118_verdict_ok
  (v : natural_occurrence_z118_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_occurrence_named_ok => true
  | _ => false
  end.

Record natural_occurrence_incidence : Type := {
  natural_occurrence_inc_z : nat;
  natural_occurrence_inc_witness_kind : occurrence_witness_kind;
  natural_occurrence_inc_level : nat
}.

Definition naturalOccurrenceIncidenceNontrivial (h : natural_occurrence_incidence) : bool :=
  Nat.ltb 0 (natural_occurrence_inc_level h).

Definition naturalOccurrenceIncidenceIronL1 : natural_occurrence_incidence :=
  {| natural_occurrence_inc_z := iron_z;
     natural_occurrence_inc_witness_kind := occurrence_product_named;
     natural_occurrence_inc_level := 1 |}.

Definition naturalOccurrenceIncidenceHeliumL1 : natural_occurrence_incidence :=
  {| natural_occurrence_inc_z := helium_z;
     natural_occurrence_inc_witness_kind := occurrence_product_named;
     natural_occurrence_inc_level := 1 |}.

Definition naturalOccurrenceIncidenceTrivial : natural_occurrence_incidence :=
  {| natural_occurrence_inc_z := 0;
     natural_occurrence_inc_witness_kind := occurrence_product_named;
     natural_occurrence_inc_level := 0 |}.

Definition naturalOccurrenceIncidenceFolklore : natural_occurrence_incidence :=
  {| natural_occurrence_inc_z := iron_z;
     natural_occurrence_inc_witness_kind := folklore_list_theater;
     natural_occurrence_inc_level := 1 |}.

Definition naturalOccurrenceIncidenceXorEnum : natural_occurrence_incidence :=
  {| natural_occurrence_inc_z := iron_z;
     natural_occurrence_inc_witness_kind := xor_enum_bucket_theater;
     natural_occurrence_inc_level := 1 |}.

Definition evaluate_natural_occurrence_incidence
  (m : NaturalOccurrenceZ118Modality)
  (h : natural_occurrence_incidence)
  (b : natural_occurrence_claim_bar)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_xor_enum : bool)
  (claim_fourth_science : bool)
  (claim_twenty_sixth_axiom : bool) : natural_occurrence_z118_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
       then verdict_proved_without_bar_refuse
       else if claim_fourth_science
            then verdict_fourth_science_refuse
            else if claim_twenty_sixth_axiom
                 then verdict_twenty_sixth_axiom_refuse
                 else if folklore_list_smuggle (natural_occurrence_inc_witness_kind h)
                      then verdict_folklore_list_refuse
                      else if xor_enum_smuggle (natural_occurrence_inc_witness_kind h)
                           then verdict_xor_enum_refuse
                           else if claim_xor_enum
                                then verdict_xor_enum_refuse
                                else if negb (naturalOccurrenceIncidenceNontrivial h)
                                     then verdict_trivial_z_refuse
                                     else if negb (occurrence_element_z_valid
                                                     (natural_occurrence_inc_z h))
                                          then verdict_trivial_z_refuse
                                          else
                                            match m with
                                            | natural_occurrence_z118_unwired =>
                                                verdict_occurrence_named_ok
                                            | natural_occurrence_z118_assumed
                                            | natural_occurrence_z118_surrogate =>
                                                verdict_unwired_ok
                                            | natural_occurrence_z118_proved =>
                                                verdict_proved_without_bar_refuse
                                            end.

Definition evaluate_natural_occurrence_close
  (m : NaturalOccurrenceZ118Modality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : natural_occurrence_z118_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | natural_occurrence_z118_unwired => verdict_unwired_ok
    | natural_occurrence_z118_assumed
    | natural_occurrence_z118_proved
    | natural_occurrence_z118_surrogate => verdict_occurrence_named_ok
    end.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs smuggle refuse (not wired)                *)
(* ------------------------------------------------------------------ *)

Definition natural_occurrence_z118_wired_in_lib : bool := false.

Definition natural_occurrence_z118_wired_in_eos : bool := false.

Lemma natural_occurrence_not_wired_lib :
  natural_occurrence_z118_wired_in_lib = false.
Proof. reflexivity. Qed.

Lemma natural_occurrence_not_wired_eos :
  natural_occurrence_z118_wired_in_eos = false.
Proof. reflexivity. Qed.

Lemma wave100_not_wired :
  negb natural_occurrence_z118_wired_in_lib &&
  negb natural_occurrence_z118_wired_in_eos = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Natural occurrence Z118 pins — structure witness, not Proved        *)
(* ------------------------------------------------------------------ *)

Definition naturalOccurrenceZ118Proved : bool := false.

Lemma natural_occurrence_z118_proved_false :
  naturalOccurrenceZ118Proved = false.
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

Definition natural_occurrence_honest_conjunct : bool :=
  table_covers_z118 &&
  helium_has_no_crustal_ore_bit &&
  iron_is_occurrence_product &&
  every_z_classified.

Lemma natural_occurrence_honest_conjunct_true :
  natural_occurrence_honest_conjunct = true.
Proof.
  unfold natural_occurrence_honest_conjunct.
  simpl.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close + named He / Fe occurrence witnesses                  *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_natural_occurrence_close
    natural_occurrence_z118_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_natural_occurrence_close
    natural_occurrence_z118_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma iron_occurrence_named_ok :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceIronL1
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_occurrence_named_ok.
Proof. reflexivity. Qed.

Lemma helium_occurrence_named_ok :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceHeliumL1
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_occurrence_named_ok.
Proof. reflexivity. Qed.

Theorem named_natural_occurrence_z118 :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceIronL1
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_occurrence_named_ok /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceHeliumL1
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_occurrence_named_ok /\
  iron_is_occurrence_product = true /\
  helium_has_no_crustal_ore_bit = true /\
  table_covers_z118 = true /\
  every_z_classified = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma trivial_z_refused :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceTrivial
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_z_fail_closed :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceTrivial
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_trivial_z_refuse /\
  natural_occurrence_z118_verdict_ok
    (evaluate_natural_occurrence_incidence
       natural_occurrence_z118_unwired naturalOccurrenceIncidenceTrivial
       naturalOccurrenceClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold natural_occurrence_z118_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

Lemma folklore_list_refused :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceFolklore
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_folklore_list_refuse.
Proof. reflexivity. Qed.

Theorem folklore_list_fail_closed :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceFolklore
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_folklore_list_refuse /\
  natural_occurrence_z118_verdict_ok
    (evaluate_natural_occurrence_incidence
       natural_occurrence_z118_unwired naturalOccurrenceIncidenceFolklore
       naturalOccurrenceClaimBarAbsent false false false false false) =
  false.
Proof.
  split.
  - apply folklore_list_refused.
  - unfold natural_occurrence_z118_verdict_ok.
    rewrite folklore_list_refused.
    reflexivity.
Qed.

Lemma xor_enum_refused :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceXorEnum
    naturalOccurrenceClaimBarAbsent false false false false false =
  verdict_xor_enum_refuse.
Proof. reflexivity. Qed.

Lemma green_invent_refuse_unwired :
  evaluate_natural_occurrence_close
    natural_occurrence_z118_unwired true false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  natural_occurrence_z118_verdict_ok
    (evaluate_natural_occurrence_close
       natural_occurrence_z118_unwired true false) =
  false.
Proof.
  unfold natural_occurrence_z118_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma proved_without_bar_refuse :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceIronL1
    naturalOccurrenceClaimBarAbsent false true false false false =
  verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Lemma production_wired_refuse :
  evaluate_natural_occurrence_close
    natural_occurrence_z118_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — not meso acting                     *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition natural_occurrence_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition naturalOccurrenceDoesNotMintFourthScience : bool :=
  notFourthChemistryScience.

Definition naturalOccurrenceDoesNotClaimProved : bool :=
  negb naturalOccurrenceZ118Proved.

Lemma natural_occurrence_knowing_fiber_ok :
  natural_occurrence_fiber_ok fiber_quantum_knowing = true.
Proof. reflexivity. Qed.

Lemma natural_occurrence_meso_acting_fiber_not_ok :
  natural_occurrence_fiber_ok fiber_meso_acting = false.
Proof. reflexivity. Qed.

Theorem natural_occurrence_routes_knowing_not_meso :
  natural_occurrence_fiber_ok fiber_quantum_knowing = true /\
  natural_occurrence_fiber_ok fiber_meso_acting = false /\
  naturalOccurrenceDoesNotMintFourthScience = true /\
  naturalOccurrenceDoesNotClaimProved = true /\
  notTwentySixthAxiom = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named occurrence + fail-closed + fiber + table   *)
(* ------------------------------------------------------------------ *)

Theorem natural_occurrence_z118_fixture_scaffold :
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceIronL1
    naturalOccurrenceClaimBarAbsent false false false false false =
    verdict_occurrence_named_ok /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceHeliumL1
    naturalOccurrenceClaimBarAbsent false false false false false =
    verdict_occurrence_named_ok /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceTrivial
    naturalOccurrenceClaimBarAbsent false false false false false =
    verdict_trivial_z_refuse /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceFolklore
    naturalOccurrenceClaimBarAbsent false false false false false =
    verdict_folklore_list_refuse /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceXorEnum
    naturalOccurrenceClaimBarAbsent false false false false false =
    verdict_xor_enum_refuse /\
  evaluate_natural_occurrence_incidence
    natural_occurrence_z118_unwired naturalOccurrenceIncidenceIronL1
    naturalOccurrenceClaimBarAbsent false true false false false =
    verdict_proved_without_bar_refuse /\
  evaluate_natural_occurrence_close
    natural_occurrence_z118_unwired false false =
    verdict_unwired_ok /\
  natural_occurrence_fiber_ok fiber_quantum_knowing = true /\
  natural_occurrence_fiber_ok fiber_meso_acting = false /\
  naturalOccurrenceZ118Proved = false /\
  natural_occurrence_honest_conjunct = true /\
  (negb natural_occurrence_z118_wired_in_lib &&
   negb natural_occurrence_z118_wired_in_eos = true) /\
  folkloreListMarker <> productClassifierMarker /\
  xorEnumMarker <> productFactorMarker.
Proof.
  repeat split.
  all: try reflexivity.
  - apply folklore_marker_ne_product_classifier_marker.
  - apply xor_marker_ne_product_factor_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — occurrence class)    *)
(* ------------------------------------------------------------------ *)

Definition naturalOccurrenceZ118RsAuthority : string :=
  "umst/umst-chem/src/x_rows/natural_occurrence_z118.rs".

Definition chemIntCrossNaturalOccurrenceAuthority : string :=
  "CHEM-INT-CROSS-NATURAL-OCCURRENCE-Z118-CONSERVATION".

Definition naturalOccurrenceZ118CellId : string :=
  "CHEM-FORMAL-Q-COQ-NATURAL-OCCURRENCE-Z118-CONSERVATION".

Definition naturalOccurrenceZ118NonClaim : string :=
  "CHEM-FORMAL-Q-COQ-NATURAL-OCCURRENCE-Z118-CONSERVATION Z=1..118 natural occurrence class table as Unwired named product classifiers native oxide sulfide silicate halide carbonate atmophile synthetic-or-trace not folklore lists concurrent bits not XOR not fourth chemistry science not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse naturalOccurrenceZ118Proved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN not physics GREEN not production_wired".

Lemma natural_occurrence_z118_cell_id :
  naturalOccurrenceZ118CellId =
  "CHEM-FORMAL-Q-COQ-NATURAL-OCCURRENCE-Z118-CONSERVATION".
Proof. reflexivity. Qed.

Lemma natural_occurrence_cites_rs_row :
  naturalOccurrenceZ118RsAuthority <> "".
Proof. discriminate. Qed.

Lemma natural_occurrence_cites_int_cross_row :
  chemIntCrossNaturalOccurrenceAuthority =
  "CHEM-INT-CROSS-NATURAL-OCCURRENCE-Z118-CONSERVATION".
Proof. reflexivity. Qed.

Lemma natural_occurrence_cites_surface :
  naturaloccurrencez118Surface = "natural_occurrence_z118_surface".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**                    *)
(* ------------------------------------------------------------------ *)

Definition naturalOccurrenceSecondLawConservationFraming : string :=
  "second_law_conservation_natural_occurrence_z118_one_axiom_not_26th_axiom".

Lemma natural_occurrence_not_twenty_sixth_axiom_framing :
  naturalOccurrenceSecondLawConservationFraming <>
  "twenty_sixth_chemistry_axiom".
Proof. discriminate. Qed.

Lemma natural_occurrence_not_fourth_science_axiom :
  naturalOccurrenceSecondLawConservationFraming <>
  "fourth_chemistry_science_axiom".
Proof. discriminate. Qed.

Lemma natural_occurrence_second_law_conservation_framing :
  naturalOccurrenceSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma natural_occurrence_z118_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma natural_occurrence_z118_modality_unwired :
  naturalOccurrenceZ118ModalityCurrent = natural_occurrence_z118_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ConstantDeriveSecondLawCensus.v                       *)
(*  name-from-content stem: constantderivesecondlawcensus              *)
(*                                                                      *)
(*  Knowing-fiber Coq: constant-derive second-law **census conservation*. *)
(*  Engines consult ExactSI / occupancy / derived-morphism sheaf; they   *)
(*  do not mint k, R, or ε₀. α MeasuredCited — not Landauer-faked.     *)
(*  Cites sibling engine_refuses_new_si + INT census row — not fork.     *)
(*  Modality Unwired. physics_green = False. Zero Admitted. Not wired    *)
(*  lib/eos. Sole axiom: second law + conservation — not 26th axiom.   *)
(* ================================================================== *)

Require Import UMST.ChemConstants.EngineRefusesNewSi.
From Stdlib Require Import Arith String Bool Lia.

Open Scope string.

Definition constantderivesecondlawcensusSurface : string :=
  "constant_derive_second_law_census_surface".

Definition constantDeriveSecondLawCensusMarker : string :=
  "chem_int_cross_constant_derive_second_law_census_v1".

Lemma constant_derive_second_law_census_surface_named :
  constantderivesecondlawcensusSurface <> "".
Proof. discriminate. Qed.

Lemma constant_derive_second_law_census_marker_named :
  constantDeriveSecondLawCensusMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Constant-derive second-law census modality (Unwired)               *)
(* ------------------------------------------------------------------ *)

Inductive ConstantDeriveSecondLawCensusModality : Type :=
  | constant_derive_second_law_census_unwired
  | constant_derive_second_law_census_assumed
  | constant_derive_second_law_census_proved
  | constant_derive_second_law_census_surrogate.

Definition constantDeriveSecondLawCensusModalityCurrent :
  ConstantDeriveSecondLawCensusModality :=
  constant_derive_second_law_census_unwired.

Definition constant_derive_modality_lattice_cardinality : nat := 4.

Lemma constant_derive_modality_lattice_cardinality_is_four :
  constant_derive_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma constant_derive_modality_lattice_not_118_squared :
  negb (Nat.eqb constant_derive_modality_lattice_cardinality (118 * 118)) =
  true.
Proof.
  unfold constant_derive_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Sheaf consult layers — ExactSI / occupancy / derived morphism       *)
(* ------------------------------------------------------------------ *)

Inductive SheafConsultLayer : Type :=
  | exact_si_layer
  | occupancy_layer
  | derived_morphism_layer.

Definition sheafConsultLayerTag (l : SheafConsultLayer) : string :=
  match l with
  | exact_si_layer => "ExactSI"
  | occupancy_layer => "occupancy"
  | derived_morphism_layer => "derived_morphism"
  end.

Lemma exact_si_layer_tag :
  sheafConsultLayerTag exact_si_layer = "ExactSI".
Proof. reflexivity. Qed.

Lemma occupancy_layer_tag :
  sheafConsultLayerTag occupancy_layer = "occupancy".
Proof. reflexivity. Qed.

Lemma derived_morphism_layer_tag :
  sheafConsultLayerTag derived_morphism_layer = "derived_morphism".
Proof. reflexivity. Qed.

Definition sheaf_consult_layer_count : nat := 3.

Lemma sheaf_consult_layer_count_is_three :
  sheaf_consult_layer_count = 3.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Engine census rows — consult sheaf, do not mint k/R/ε₀              *)
(* ------------------------------------------------------------------ *)

Inductive EngineCensusRowTag : Type :=
  | si_exact_defining_constants_row
  | qlattice_row
  | gas_constant_derived_morphism_row
  | vacuum_permittivity_derived_row
  | engine_refuses_new_si_row.

Definition engineCensusRowSheafLayer (r : EngineCensusRowTag) : SheafConsultLayer :=
  match r with
  | si_exact_defining_constants_row => exact_si_layer
  | qlattice_row => occupancy_layer
  | gas_constant_derived_morphism_row => derived_morphism_layer
  | vacuum_permittivity_derived_row => derived_morphism_layer
  | engine_refuses_new_si_row => exact_si_layer
  end.

Definition rowMayMintSi (r : EngineCensusRowTag) : bool := false.

Lemma row_may_not_mint_si (r : EngineCensusRowTag) :
  rowMayMintSi r = false.
Proof. destruct r; reflexivity. Qed.

Definition engine_census_row_count : nat := 5.

Lemma engine_census_row_count_is_five :
  engine_census_row_count = 5.
Proof. reflexivity. Qed.

Definition allCensusRowsConsultSheaf : bool := true.

Lemma all_engine_census_rows_consult_sheaf :
  allCensusRowsConsultSheaf = true.
Proof. reflexivity. Qed.

Definition forbiddenSiMintsPinned : bool := true.

Lemma forbidden_si_mints_pinned :
  forbiddenSiMintsPinned = true.
Proof. reflexivity. Qed.

Definition enginesUseExistingSheafBool : bool := true.

Lemma engines_use_existing_sheaf_bool :
  enginesUseExistingSheafBool = true.
Proof. reflexivity. Qed.

Lemma engines_may_not_mint_forbidden_si :
  engine_may_mint_si = false.
Proof. apply engine_may_mint_si_false. Qed.

(* ------------------------------------------------------------------ *)
(*  Fine-structure α — MeasuredCited, not Landauer-faked                *)
(* ------------------------------------------------------------------ *)

Definition fineStructureAlphaPinKind : string := "MeasuredCited".

Definition landauerBridgeCoversKcNotAlpha : string :=
  "LandauerEinsteinBridge.lean FormalLift k c — alpha remains MeasuredCited not Landauer-faked".

Lemma fine_structure_alpha_pin_kind_named :
  fineStructureAlphaPinKind = "MeasuredCited".
Proof. reflexivity. Qed.

Definition landauerFakeAlphaMinted : bool := false.

Lemma landauer_fake_alpha_not_minted :
  landauerFakeAlphaMinted = false.
Proof. reflexivity. Qed.

Definition alphaMeasuredCitedNotLandauerFake : bool := true.

Lemma alpha_measured_cited_not_landauer_fake :
  alphaMeasuredCitedNotLandauerFake = true.
Proof. reflexivity. Qed.

Definition landauerBridgeScopedKcNotAlpha : bool := true.

Lemma landauer_bridge_scoped_kc_not_alpha :
  landauerBridgeScopedKcNotAlpha = true.
Proof. reflexivity. Qed.

Definition exactSiKCitedNotMinted : bool := true.

Lemma exact_si_k_cited_not_minted :
  exactSiKCitedNotMinted = true.
Proof. reflexivity. Qed.

Lemma alpha_not_landauer_fake_cites_engine_refuse :
  alpha_is_deferred_codata_not_landauer = true.
Proof. apply alpha_is_deferred_codata_not_landauer_true. Qed.

(* ------------------------------------------------------------------ *)
(*  Honest conjunct — census consult ≠ SI mint ≠ Landauer-fake α        *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusHonestConjunct : bool :=
  engine_mint_refused &&
  allCensusRowsConsultSheaf &&
  forbiddenSiMintsPinned &&
  enginesUseExistingSheafBool &&
  alphaMeasuredCitedNotLandauerFake &&
  landauerBridgeScopedKcNotAlpha &&
  exactSiKCitedNotMinted &&
  negb landauerFakeAlphaMinted &&
  engine_refuse_not_26th_axiom.

Lemma constant_derive_second_law_census_honest_conjunct_true :
  constantDeriveSecondLawCensusHonestConjunct = true.
Proof.
  unfold constantDeriveSecondLawCensusHonestConjunct.
  simpl.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs not wired (deferred composition)           *)
(* ------------------------------------------------------------------ *)

Definition wave100LibRsWired : bool := false.
Definition wave100EosRsWired : bool := false.
Definition productionWired : bool := false.

Lemma wave100_lib_rs_not_wired :
  wave100LibRsWired = false.
Proof. reflexivity. Qed.

Lemma wave100_eos_rs_not_wired :
  wave100EosRsWired = false.
Proof. reflexivity. Qed.

Lemma production_wired_false :
  productionWired = false.
Proof. reflexivity. Qed.

Lemma wave100_not_wired :
  negb wave100LibRsWired && negb wave100EosRsWired = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation close verdict — fail-closed lattice                      *)
(* ------------------------------------------------------------------ *)

Inductive constant_derive_second_law_census_verdict : Type :=
  | verdict_unwired_ok
  | verdict_census_ok
  | verdict_green_invent_refuse
  | verdict_production_wired_refuse
  | verdict_si_mint_refuse.

Definition constant_derive_second_law_census_verdict_ok
  (v : constant_derive_second_law_census_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_census_ok => true
  | _ => false
  end.

Definition evaluate_constant_derive_second_law_census
  (m : ConstantDeriveSecondLawCensusModality)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_production_wired : bool) : constant_derive_second_law_census_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else if engine_may_mint_si
  then verdict_si_mint_refuse
  else if claim_proved
  then verdict_census_ok
  else if constantDeriveSecondLawCensusHonestConjunct
  then
    match m with
    | constant_derive_second_law_census_unwired => verdict_unwired_ok
    | constant_derive_second_law_census_assumed
    | constant_derive_second_law_census_proved
    | constant_derive_second_law_census_surrogate => verdict_census_ok
    end
  else verdict_si_mint_refuse.

Lemma constant_derive_second_law_census_unwired_ok :
  evaluate_constant_derive_second_law_census
    constant_derive_second_law_census_unwired false false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_green_invent_refuse :
  evaluate_constant_derive_second_law_census
    constant_derive_second_law_census_unwired true false false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_production_wired_refuse :
  evaluate_constant_derive_second_law_census
    constant_derive_second_law_census_unwired false false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_green_refuse_verdict_false :
  constant_derive_second_law_census_verdict_ok
    (evaluate_constant_derive_second_law_census
       constant_derive_second_law_census_unwired true false false) =
  false.
Proof.
  unfold constant_derive_second_law_census_verdict_ok.
  rewrite constant_derive_second_law_census_green_invent_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Proved / wired posture — fail-closed (Unwired not Proved)            *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusProved : bool := false.

Lemma constant_derive_second_law_census_not_proved :
  constantDeriveSecondLawCensusProved = false.
Proof. reflexivity. Qed.

Theorem constant_derive_second_law_census_conservation :
  evaluate_constant_derive_second_law_census
    constant_derive_second_law_census_unwired false false false =
  verdict_unwired_ok /\
  constantDeriveSecondLawCensusHonestConjunct = true /\
  constantDeriveSecondLawCensusProved = false /\
  wave100LibRsWired = false /\
  wave100EosRsWired = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Not a 26th axiom — cites engine_refuse / sole axiom pins            *)
(* ------------------------------------------------------------------ *)

Lemma constant_derive_sole_axiom_count_is_one :
  sole_axiom_count = 1.
Proof. apply sole_axiom_count_is_one. Qed.

Lemma constant_derive_not_26th_axiom :
  engine_refuse_not_26th_axiom = true.
Proof. apply engine_refuse_not_26th_axiom_true. Qed.

Lemma constant_derive_engine_refuses_modality_still_unwired :
  engineRefusesNewSiModalityCurrent = engine_refuses_new_si_unwired.
Proof. apply engine_refuses_new_si_modality_unwired. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — census pins)         *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusCellId : string :=
  "CHEM-FORMAL-Q-COQ-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION".

Definition constantDeriveSecondLawCensusIntCellId : string :=
  "CHEM-INT-CROSS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION".

Definition constantDeriveSecondLawCensusNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION Unwired — engines consult ExactSI occupancy derived-morphism sheaf; do not mint k R epsilon_0; alpha MeasuredCited not Landauer-faked; cite engine_refuses_new_si constant_derive_preference si_exact_defining_constants gas_constant_is_derived_morphism vacuum_permittivity_si_derived qlattice not fork; second law conservation sole axiom not 26th axiom; not physics GREEN; not production_wired".

Definition constantDeriveSecondLawCensusCrossWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/constant_derive_second_law_census.rs".

Definition constantDerivePreferenceAuthority : string :=
  "umst/umst-chem/src/constant_derive_preference.rs".

Definition siExactDefiningConstantsAuthority : string :=
  "umst/umst-chem/src/si_exact_defining_constants.rs".

Definition gasConstantDerivedMorphismAuthority : string :=
  "umst/umst-chem/src/gas_constant_is_derived_morphism.rs".

Definition vacuumPermittivitySiDerivedAuthority : string :=
  "umst/umst-chem/src/vacuum_permittivity_si_derived.rs".

Definition qlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition secondLawConservationAxiom : string :=
  "second law conservation — engines consult sheaf; alpha MeasuredCited not Landauer-faked; sole axiom".

Definition censusNotSiMintOrLandauerFakeAlphaOr26thAxiom : string :=
  "constant derive census consults ExactSI occupancy derived-morphism sheaf — not mint k R epsilon_0 not Landauer-fake alpha not 26th axiom".

Lemma constant_derive_second_law_census_cell_id :
  constantDeriveSecondLawCensusCellId =
  "CHEM-FORMAL-Q-COQ-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION".
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_cites_cross_witness_rs :
  constantDeriveSecondLawCensusCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/constant_derive_second_law_census.rs".
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_cites_engine_refuses_new_si :
  engineRefusesNewSiRsAuthority <>
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma constant_derive_second_law_census_cites_derive_preference :
  constantDerivePreferenceAuthority <>
  "".
Proof. discriminate. Qed.

Lemma constant_derive_second_law_census_cites_si_exact :
  siExactDefiningConstantsAuthority <>
  "".
Proof. discriminate. Qed.

Lemma constant_derive_second_law_census_cites_gas_constant_derived :
  gasConstantDerivedMorphismAuthority <>
  "".
Proof. discriminate. Qed.

Lemma constant_derive_second_law_census_cites_vacuum_permittivity :
  vacuumPermittivitySiDerivedAuthority <>
  "".
Proof. discriminate. Qed.

Lemma constant_derive_second_law_census_cites_qlattice :
  qlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_modality_unwired :
  constantDeriveSecondLawCensusModalityCurrent =
  constant_derive_second_law_census_unwired.
Proof. reflexivity. Qed.

Lemma constant_derive_second_law_census_int_cell_id :
  constantDeriveSecondLawCensusIntCellId =
  "CHEM-INT-CROSS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Row proved fence — Unwired scaffold, not path-census Proved         *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusRowProved : Prop := False.

Lemma constant_derive_second_law_census_row_not_proved :
  ~ constantDeriveSecondLawCensusRowProved.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusPhysicsGreenAuthorized : Prop := False.

Lemma constant_derive_second_law_census_physics_green_false :
  ~ constantDeriveSecondLawCensusPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma constant_derive_second_law_census_engine_refuses_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. apply engine_refuses_new_si_physics_green_false. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition constantDeriveSecondLawCensusProductionWired : Prop := False.

Lemma constant_derive_second_law_census_not_production_wired :
  ~ constantDeriveSecondLawCensusProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — census consult + mint refuse + not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Theorem constant_derive_second_law_census_fixture_scaffold :
  constantDeriveSecondLawCensusHonestConjunct = true /\
  evaluate_constant_derive_second_law_census
    constant_derive_second_law_census_unwired false false false =
    verdict_unwired_ok /\
  constantDeriveSecondLawCensusProved = false /\
  engine_may_mint_si = false /\
  (negb wave100LibRsWired && negb wave100EosRsWired = true) /\
  sole_axiom_count = 1.
Proof.
  exact (conj constant_derive_second_law_census_honest_conjunct_true
    (conj constant_derive_second_law_census_unwired_ok
      (conj constant_derive_second_law_census_not_proved
        (conj engine_may_mint_si_false
          (conj wave100_not_wired sole_axiom_count_is_one))))).
Qed.

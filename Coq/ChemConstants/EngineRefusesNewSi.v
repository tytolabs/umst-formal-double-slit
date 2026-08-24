(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EngineRefusesNewSi.v                                  *)
(*  name-from-content stem: enginerefusesnewsi                         *)
(*                                                                      *)
(*  Knowing-fiber Coq: constitutive engines sort using the existing    *)
(*  SI/occupancy/derived-morphism sheaf; they do not mint k, R, or ε₀. *)
(*  α at current depth is deferred composition (CODATA), not Landauer-  *)
(*  fake, not a 26th axiom. GREEN invent fail-closed; Proved-without-  *)
(*  bar fail-closed. engineRefusesNewSiProved false. Modality Unwired.   *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing — engine refuse is   *)
(*  not a second axiom. Not a 118² GREEN table.                         *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

Definition enginerefusesnewsiSurface : string :=
  "engine_refuses_new_si_surface".

Lemma enginerefusesnewsi_surface_named :
  enginerefusesnewsiSurface <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved / Surrogate modality lattice                                  *)
(* ------------------------------------------------------------------ *)

Inductive EngineRefusesNewSiModality : Type :=
  | engine_refuses_new_si_unwired
  | engine_refuses_new_si_assumed
  | engine_refuses_new_si_proved
  | engine_refuses_new_si_surrogate.

Definition engineRefusesNewSiModalityCurrent : EngineRefusesNewSiModality :=
  engine_refuses_new_si_unwired.

Definition engine_refuses_modality_lattice_cardinality : nat := 4.

Lemma engine_refuses_modality_lattice_cardinality_is_four :
  engine_refuses_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma engine_refuses_modality_lattice_not_118_squared :
  negb (Nat.eqb engine_refuses_modality_lattice_cardinality (118 * 118)) =
  true.
Proof.
  unfold engine_refuses_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Forbidden SI mints — k, R, ε₀ (engines consult sheaf, do not mint)  *)
(* ------------------------------------------------------------------ *)

Definition forbidden_si_mint_k : string := "k".
Definition forbidden_si_mint_R : string := "R".
Definition forbidden_si_mint_epsilon_0 : string := "epsilon_0".

Definition forbidden_si_mint_count : nat := 3.

Lemma forbidden_si_mint_count_is_three :
  forbidden_si_mint_count = 3.
Proof. reflexivity. Qed.

Lemma forbidden_mint_k_named : forbidden_si_mint_k = "k".
Proof. reflexivity. Qed.

Lemma forbidden_mint_R_named : forbidden_si_mint_R = "R".
Proof. reflexivity. Qed.

Lemma forbidden_mint_epsilon_0_named :
  forbidden_si_mint_epsilon_0 = "epsilon_0".
Proof. reflexivity. Qed.

Lemma forbidden_mints_distinct_k_R :
  forbidden_si_mint_k <> forbidden_si_mint_R.
Proof. discriminate. Qed.

Lemma forbidden_mints_distinct_k_epsilon :
  forbidden_si_mint_k <> forbidden_si_mint_epsilon_0.
Proof. discriminate. Qed.

Lemma forbidden_mints_distinct_R_epsilon :
  forbidden_si_mint_R <> forbidden_si_mint_epsilon_0.
Proof. discriminate. Qed.

Definition engine_may_mint_si : bool := false.

Lemma engine_may_mint_si_false : engine_may_mint_si = false.
Proof. reflexivity. Qed.

Definition engine_uses_existing_sheaf : bool :=
  negb engine_may_mint_si &&
  Nat.eqb forbidden_si_mint_count 3.

Lemma engine_uses_existing_sheaf_true : engine_uses_existing_sheaf = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SI / occupancy / derived-morphism sheaf consult markers             *)
(* ------------------------------------------------------------------ *)

Definition si_sheaf_marker : string :=
  "si_occupancy_derived_morphism_sheaf_consult_v1".

Definition occupancy_sheaf_marker : string :=
  "occupancy_engine_sort_sheaf_consult_v1".

Definition derived_morphism_sheaf_marker : string :=
  "derived_morphism_sheaf_consult_v1".

Lemma si_sheaf_marker_named : si_sheaf_marker <> "".
Proof. discriminate. Qed.

Lemma occupancy_sheaf_marker_named : occupancy_sheaf_marker <> "".
Proof. discriminate. Qed.

Lemma derived_morphism_sheaf_marker_named :
  derived_morphism_sheaf_marker <> "".
Proof. discriminate. Qed.

Lemma sheaf_markers_distinct_si_occupancy :
  si_sheaf_marker <> occupancy_sheaf_marker.
Proof. discriminate. Qed.

Definition engine_sorts_via_sheaf : bool :=
  engine_uses_existing_sheaf &&
  negb (String.eqb si_sheaf_marker "") &&
  negb (String.eqb occupancy_sheaf_marker "") &&
  negb (String.eqb derived_morphism_sheaf_marker "").

Lemma engine_sorts_via_sheaf_true : engine_sorts_via_sheaf = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  α deferred composition (CODATA) — not Landauer-fake                   *)
(* ------------------------------------------------------------------ *)

Definition alpha_deferred_codata_marker : string :=
  "alpha_deferred_composition_codata_not_landauer_fake_v1".

Definition landauer_fake_marker : string :=
  "landauer_fake_alpha_mint_v1".

Lemma alpha_deferred_codata_marker_named :
  alpha_deferred_codata_marker <> "".
Proof. discriminate. Qed.

Lemma alpha_not_landauer_fake :
  alpha_deferred_codata_marker <> landauer_fake_marker.
Proof. discriminate. Qed.

Definition alpha_is_deferred_codata_not_landauer : bool :=
  negb (String.eqb alpha_deferred_codata_marker landauer_fake_marker).

Lemma alpha_is_deferred_codata_not_landauer_true :
  alpha_is_deferred_codata_not_landauer = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not a 26th axiom — second law + conservation framing only             *)
(* ------------------------------------------------------------------ *)

Definition twenty_sixth_axiom_marker : string := "twenty_sixth_axiom_v1".

Definition sole_axiom_count : nat := 1.

Lemma sole_axiom_count_is_one : sole_axiom_count = 1.
Proof. reflexivity. Qed.

Lemma not_twenty_sixth_axiom :
  Nat.eqb sole_axiom_count 26 = false.
Proof. reflexivity. Qed.

Definition engine_refuse_not_26th_axiom : bool :=
  negb (Nat.eqb sole_axiom_count 26).

Lemma engine_refuse_not_26th_axiom_true :
  engine_refuse_not_26th_axiom = true.
Proof. reflexivity. Qed.

Lemma twenty_sixth_axiom_marker_ne_sole :
  twenty_sixth_axiom_marker <> "sole_axiom_second_law_conservation".
Proof. discriminate. Qed.

Definition EngineRefusesNewSiSecondLawConservationFraming : string :=
  "second_law_conservation_engine_refuse_one_axiom_not_26th_axiom".

Lemma engine_refuse_not_second_axiom :
  EngineRefusesNewSiSecondLawConservationFraming <>
  "second_engine_refuse_axiom".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Mint refuse — engines do not author new defining constants          *)
(* ------------------------------------------------------------------ *)

Definition new_si_mint_marker : string :=
  "engine_mints_new_si_defining_constant_v1".

Definition sheaf_consult_marker : string :=
  "engine_consults_existing_sheaf_v1".

Lemma new_si_mint_marker_ne_sheaf_consult :
  new_si_mint_marker <> sheaf_consult_marker.
Proof. discriminate. Qed.

Definition engine_mint_refused : bool :=
  negb engine_may_mint_si.

Lemma engine_mint_refused_true : engine_mint_refused = true.
Proof. reflexivity. Qed.

Definition engine_refuses_new_si_honest_conjunct : bool :=
  engine_mint_refused &&
  engine_uses_existing_sheaf &&
  engine_sorts_via_sheaf &&
  alpha_is_deferred_codata_not_landauer &&
  engine_refuse_not_26th_axiom.

Lemma engine_refuses_new_si_honest_conjunct_true :
  engine_refuses_new_si_honest_conjunct = true.
Proof.
  unfold engine_refuses_new_si_honest_conjunct.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem engine_refuses_new_si_mint_and_sheaf :
  engine_mint_refused = true /\
  engine_uses_existing_sheaf = true /\
  forbidden_si_mint_count = 3.
Proof.
  exact (conj engine_mint_refused_true
    (conj engine_uses_existing_sheaf_true forbidden_si_mint_count_is_three)).
Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs smuggle refuse (not wired)                *)
(* ------------------------------------------------------------------ *)

Definition wave100_lib_smuggle_marker : string :=
  "wave100_lib_rs_eos_rs_smuggle_refuse_v1".

Definition engine_refuses_wired_in_lib : bool := false.
Definition engine_refuses_wired_in_eos : bool := false.

Lemma engine_refuses_not_wired_lib :
  engine_refuses_wired_in_lib = false.
Proof. reflexivity. Qed.

Lemma engine_refuses_not_wired_eos :
  engine_refuses_wired_in_eos = false.
Proof. reflexivity. Qed.

Lemma wave100_not_wired :
  negb engine_refuses_wired_in_lib &&
  negb engine_refuses_wired_in_eos = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Engine refuse conservation verdict — fail-closed lattice              *)
(* ------------------------------------------------------------------ *)

Inductive engine_refuses_verdict : Type :=
  | verdict_unwired_ok
  | verdict_engine_refuse_named_ok
  | verdict_si_mint_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse
  | verdict_26th_axiom_refuse
  | verdict_landauer_fake_refuse.

Definition engine_refuses_verdict_ok (v : engine_refuses_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_engine_refuse_named_ok => true
  | _ => false
  end.

Definition evaluate_engine_refuses_close
  (m : EngineRefusesNewSiModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool)
  (claim_mint_si : bool)
  (claim_26th_axiom : bool)
  (claim_landauer_fake : bool) : engine_refuses_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else if claim_mint_si
  then verdict_si_mint_refuse
  else if claim_26th_axiom
  then verdict_26th_axiom_refuse
  else if claim_landauer_fake
  then verdict_landauer_fake_refuse
  else
    match m with
    | engine_refuses_new_si_unwired => verdict_unwired_ok
    | engine_refuses_new_si_assumed
    | engine_refuses_new_si_proved
    | engine_refuses_new_si_surrogate => verdict_engine_refuse_named_ok
    end.

Lemma unwired_close_without_claims :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false false false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_claims :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false false false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_claims. Qed.

Lemma green_invent_refuse_unwired :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired true false false false false =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  engine_refuses_verdict_ok
    (evaluate_engine_refuses_close
       engine_refuses_new_si_unwired true false false false false) =
  false.
Proof.
  unfold engine_refuses_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma si_mint_refuse :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false true false false =
  verdict_si_mint_refuse.
Proof. reflexivity. Qed.

Lemma production_wired_refuse :
  evaluate_engine_refuses_close
    engine_refuses_new_si_proved false true false false false =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Lemma twenty_sixth_axiom_refuse :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false false true false =
  verdict_26th_axiom_refuse.
Proof. reflexivity. Qed.

Lemma landauer_fake_refuse :
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false false false true =
  verdict_landauer_fake_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Engine refuse proved pin — structure witness, not Proved              *)
(* ------------------------------------------------------------------ *)

Definition engineRefusesNewSiProved : bool := false.

Lemma engine_refuses_new_si_proved_false : engineRefusesNewSiProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Matter vs knowing fiber routing                                     *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_matter_constitutive
  | fiber_quantum_knowing.

Definition engine_refuses_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_matter_constitutive => true
  | fiber_quantum_knowing => true
  end.

Lemma engine_refuses_matter_fiber_ok :
  engine_refuses_fiber_ok fiber_matter_constitutive = true.
Proof. reflexivity. Qed.

Lemma engine_refuses_knowing_fiber_ok :
  engine_refuses_fiber_ok fiber_quantum_knowing = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — sheaf consult + mint refuse + not 26th axiom     *)
(* ------------------------------------------------------------------ *)

Theorem engine_refuses_new_si_fixture_scaffold :
  engine_refuses_new_si_honest_conjunct = true /\
  evaluate_engine_refuses_close
    engine_refuses_new_si_unwired false false false false false =
    verdict_unwired_ok /\
  engineRefusesNewSiProved = false /\
  engine_may_mint_si = false /\
  (negb engine_refuses_wired_in_lib &&
   negb engine_refuses_wired_in_eos = true).
Proof.
  exact (conj engine_refuses_new_si_honest_conjunct_true
    (conj unwired_close_without_claims
      (conj engine_refuses_new_si_proved_false
        (conj engine_may_mint_si_false wave100_not_wired)))).
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — engine refuse)         *)
(* ------------------------------------------------------------------ *)

Definition engineRefusesNewSiRsAuthority : string :=
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs".

Definition chemIntCrossEngineRefusesAuthority : string :=
  "CHEM-INT-CROSS-ENGINE-REFUSES-NEW-SI-CONSERVATION".

Definition chemL0ServiceAuthority : string :=
  "CHEM-L0-SERVICE".

Definition engineRefusesNewSiCellId : string :=
  "CHEM-FORMAL-Q-COQ-ENGINE-REFUSES-NEW-SI-CONSERVATION".

Definition engineRefusesNewSiNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ENGINE-REFUSES-NEW-SI-CONSERVATION constitutive engines sort using existing SI occupancy derived-morphism sheaf do not mint k R epsilon_0 alpha deferred CODATA not Landauer-fake not 26th axiom engineRefusesNewSiProved false Unwired WAVE100 lib eos smuggle refuse one axiom second law conservation not second engine refuse axiom not GREEN DFT not physics GREEN not production_wired".

Lemma engine_refuses_new_si_cell_id :
  engineRefusesNewSiCellId =
  "CHEM-FORMAL-Q-COQ-ENGINE-REFUSES-NEW-SI-CONSERVATION".
Proof. reflexivity. Qed.

Lemma engine_refuses_cites_rs_row :
  engineRefusesNewSiRsAuthority <> "".
Proof. discriminate. Qed.

Lemma engine_refuses_cites_int_cross_row :
  chemIntCrossEngineRefusesAuthority =
  "CHEM-INT-CROSS-ENGINE-REFUSES-NEW-SI-CONSERVATION".
Proof. reflexivity. Qed.

Lemma engine_refuses_cites_l0_service :
  chemL0ServiceAuthority = "CHEM-L0-SERVICE".
Proof. reflexivity. Qed.

Lemma engine_refuses_cites_sheaf_marker :
  si_sheaf_marker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma engine_refuses_new_si_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma engine_refuses_new_si_modality_unwired :
  engineRefusesNewSiModalityCurrent = engine_refuses_new_si_unwired.
Proof. reflexivity. Qed.

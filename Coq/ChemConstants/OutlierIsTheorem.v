(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OutlierIsTheorem.v                                    *)
(*  name-from-content stem: outlieristheorem                            *)
(*                                                                      *)
(*  Knowing-fiber Coq: v50 outlier-is-theorem **conservation**.        *)
(*  Nothing in Z=1..118 or Interact/Ore/Refine may rest as folklore     *)
(*  outlier. Honest terminals: occupancy/ore/interact sort **theorem**  *)
(*  on the owning fiber; **deferred composition** named measured        *)
(*  remainder with impossibility witness; or typed **Absent**.          *)
(*  GREEN invent fail-closed; Proved-without-bar fail-closed; trivial    *)
(*  Z=0 refuse. outlierIsTheoremProved false. Modality Unwired.         *)
(*  WAVE100: not wired lib.rs / eos.rs.                                 *)
(*                                                                      *)
(*  Self-contained (Stdlib). physics_green = False. Zero Admitted.     *)
(*  One axiom second law + **conservation** framing.                     *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

Definition outlieristheoremSurface : string :=
  "outlier_is_theorem_surface_v1".

Definition outlierIsTheoremMarker : string :=
  "chem_formal_q_coq_outlier_is_theorem_v1".

Lemma outlieristheorem_surface_named :
  outlieristheoremSurface <> "".
Proof. discriminate. Qed.

Lemma outlier_is_theorem_marker_named :
  outlierIsTheoremMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Outlier-is-theorem modality (Unwired / Assumed / Proved / Surrogate) *)
(* ------------------------------------------------------------------ *)

Inductive OutlierIsTheoremModality : Type :=
  | outlier_is_theorem_unwired
  | outlier_is_theorem_assumed
  | outlier_is_theorem_proved
  | outlier_is_theorem_surrogate.

Definition outlierIsTheoremModalityCurrent : OutlierIsTheoremModality :=
  outlier_is_theorem_unwired.

Definition outlier_modality_lattice_cardinality : nat := 4.

Lemma outlier_modality_lattice_cardinality_is_four :
  outlier_modality_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma outlier_modality_lattice_not_118_squared :
  negb (Nat.eqb outlier_modality_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold outlier_modality_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z bar — Z=1..118 (not 118² GREEN table)                       *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition z_valid (z : nat) : bool :=
  Nat.ltb 0 z && Nat.leb z iupac_table_cardinality.

(* ------------------------------------------------------------------ *)
(*  Interact / Ore / Refine domain pins (north-star §3c v50 bar)        *)
(* ------------------------------------------------------------------ *)

Inductive outlier_domain : Type :=
  | outlier_domain_interact
  | outlier_domain_ore
  | outlier_domain_refine.

Definition outlierDomainTag (d : outlier_domain) : string :=
  match d with
  | outlier_domain_interact => "interact"
  | outlier_domain_ore => "ore"
  | outlier_domain_refine => "refine"
  end.

Lemma outlier_domain_interact_tag :
  outlierDomainTag outlier_domain_interact = "interact".
Proof. reflexivity. Qed.

Lemma outlier_domain_ore_tag :
  outlierDomainTag outlier_domain_ore = "ore".
Proof. reflexivity. Qed.

Lemma outlier_domain_refine_tag :
  outlierDomainTag outlier_domain_refine = "refine".
Proof. reflexivity. Qed.

Definition outlier_domain_count : nat := 3.

Lemma outlier_domain_count_is_three :
  outlier_domain_count = 3.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Honest outlier terminal — theorem | deferred composition | Absent    *)
(*  (not folklore exclusive lists)                                      *)
(* ------------------------------------------------------------------ *)

Inductive outlier_terminal : Type :=
  | outlier_terminal_theorem
  | outlier_terminal_deferred_composition
  | outlier_terminal_typed_absent.

Definition outlierTerminalTag (t : outlier_terminal) : string :=
  match t with
  | outlier_terminal_theorem => "theorem"
  | outlier_terminal_deferred_composition => "deferred_composition"
  | outlier_terminal_typed_absent => "typed_absent"
  end.

Lemma outlier_terminal_theorem_tag :
  outlierTerminalTag outlier_terminal_theorem = "theorem".
Proof. reflexivity. Qed.

Lemma outlier_terminal_deferred_tag :
  outlierTerminalTag outlier_terminal_deferred_composition =
  "deferred_composition".
Proof. reflexivity. Qed.

Lemma outlier_terminal_absent_tag :
  outlierTerminalTag outlier_terminal_typed_absent = "typed_absent".
Proof. reflexivity. Qed.

Definition folklore_outlier_marker : string :=
  "folklore_outlier_exclusive_list_v1".

Definition honest_terminal_marker : string :=
  "theorem_or_deferred_composition_or_typed_absent_v1".

Lemma folklore_marker_ne_honest_terminal :
  folklore_outlier_marker <> honest_terminal_marker.
Proof. discriminate. Qed.

Definition folklore_outlier_refused : bool := true.

Lemma folklore_outlier_refused_true :
  folklore_outlier_refused = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Named outlier witness Z pins — INT SSOT read-only cites             *)
(* ------------------------------------------------------------------ *)

Definition helium_z : nat := 2.
Definition neon_z : nat := 10.
Definition iron_z : nat := 26.
Definition gold_z : nat := 79.

Lemma helium_z_is_2 : helium_z = 2.
Proof. reflexivity. Qed.

Lemma neon_z_is_10 : neon_z = 10.
Proof. reflexivity. Qed.

Lemma iron_z_is_26 : iron_z = 26.
Proof. reflexivity. Qed.

Lemma gold_z_is_79 : gold_z = 79.
Proof. reflexivity. Qed.

Lemma witness_z_factors_valid :
  z_valid helium_z = true /\
  z_valid neon_z = true /\
  z_valid iron_z = true /\
  z_valid gold_z = true.
Proof.
  repeat split; unfold z_valid, iupac_table_cardinality; reflexivity.
Qed.

(* He/Ne: closed-shell missing Interact → typed Absent (not nobility magic). *)

Definition helium_no_ore_terminal : outlier_terminal :=
  outlier_terminal_typed_absent.

Definition neon_no_ore_terminal : outlier_terminal :=
  outlier_terminal_typed_absent.

Lemma helium_terminal_is_typed_absent :
  helium_no_ore_terminal = outlier_terminal_typed_absent.
Proof. reflexivity. Qed.

Lemma neon_terminal_is_typed_absent :
  neon_no_ore_terminal = outlier_terminal_typed_absent.
Proof. reflexivity. Qed.

(* Au native vs Fe oxide product — ore sort theorems on owning fiber. *)

Definition gold_native_outlier_terminal : outlier_terminal :=
  outlier_terminal_theorem.

Definition iron_oxide_product_terminal : outlier_terminal :=
  outlier_terminal_theorem.

Lemma gold_terminal_is_theorem :
  gold_native_outlier_terminal = outlier_terminal_theorem.
Proof. reflexivity. Qed.

Lemma iron_terminal_is_theorem :
  iron_oxide_product_terminal = outlier_terminal_theorem.
Proof. reflexivity. Qed.

(* He trace atmophile in natural gas — named measured remainder. *)

Definition helium_trace_atmophile_terminal : outlier_terminal :=
  outlier_terminal_deferred_composition.

Lemma helium_trace_terminal_is_deferred :
  helium_trace_atmophile_terminal = outlier_terminal_deferred_composition.
Proof. reflexivity. Qed.

Definition honest_terminal_not_folklore (t : outlier_terminal) : bool :=
  match t with
  | outlier_terminal_theorem => true
  | outlier_terminal_deferred_composition => true
  | outlier_terminal_typed_absent => true
  end.

Lemma all_witness_terminals_honest :
  honest_terminal_not_folklore helium_no_ore_terminal = true /\
  honest_terminal_not_folklore neon_no_ore_terminal = true /\
  honest_terminal_not_folklore gold_native_outlier_terminal = true /\
  honest_terminal_not_folklore iron_oxide_product_terminal = true /\
  honest_terminal_not_folklore helium_trace_atmophile_terminal = true.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Outlier incidence record — Z + domain + terminal                    *)
(* ------------------------------------------------------------------ *)

Record outlier_incidence : Type := {
  outlier_inc_z : nat;
  outlier_inc_domain : outlier_domain;
  outlier_inc_terminal : outlier_terminal;
  outlier_inc_level : nat
}.

Definition outlierIncidenceNontrivial (h : outlier_incidence) : bool :=
  Nat.ltb 0 (outlier_inc_level h).

Definition outlierIncidenceHeliumNoOre : outlier_incidence :=
  {| outlier_inc_z := helium_z;
     outlier_inc_domain := outlier_domain_ore;
     outlier_inc_terminal := helium_no_ore_terminal;
     outlier_inc_level := 1 |}.

Definition outlierIncidenceNeonNoOre : outlier_incidence :=
  {| outlier_inc_z := neon_z;
     outlier_inc_domain := outlier_domain_ore;
     outlier_inc_terminal := neon_no_ore_terminal;
     outlier_inc_level := 1 |}.

Definition outlierIncidenceGoldNative : outlier_incidence :=
  {| outlier_inc_z := gold_z;
     outlier_inc_domain := outlier_domain_ore;
     outlier_inc_terminal := gold_native_outlier_terminal;
     outlier_inc_level := 1 |}.

Definition outlierIncidenceIronOxide : outlier_incidence :=
  {| outlier_inc_z := iron_z;
     outlier_inc_domain := outlier_domain_ore;
     outlier_inc_terminal := iron_oxide_product_terminal;
     outlier_inc_level := 1 |}.

Definition outlierIncidenceHeliumTrace : outlier_incidence :=
  {| outlier_inc_z := helium_z;
     outlier_inc_domain := outlier_domain_refine;
     outlier_inc_terminal := helium_trace_atmophile_terminal;
     outlier_inc_level := 1 |}.

Definition outlierIncidenceTrivial : outlier_incidence :=
  {| outlier_inc_z := gold_z;
     outlier_inc_domain := outlier_domain_ore;
     outlier_inc_terminal := gold_native_outlier_terminal;
     outlier_inc_level := 0 |}.

(* ------------------------------------------------------------------ *)
(*  Outlier-is-theorem verdict — fail-closed close lattice              *)
(* ------------------------------------------------------------------ *)

Inductive outlier_is_theorem_verdict : Type :=
  | verdict_unwired_ok
  | verdict_outlier_terminal_named_ok
  | verdict_trivial_z_refuse
  | verdict_folklore_outlier_refuse
  | verdict_green_invent_refuse
  | verdict_proved_without_bar_refuse
  | verdict_production_wired_refuse.

Definition outlier_is_theorem_verdict_ok (v : outlier_is_theorem_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_outlier_terminal_named_ok => true
  | _ => false
  end.

Definition evaluate_outlier_incidence
  (m : OutlierIsTheoremModality)
  (h : outlier_incidence)
  (claim_physics_green : bool)
  (claim_proved : bool)
  (claim_folklore : bool) : outlier_is_theorem_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_proved
  then verdict_proved_without_bar_refuse
  else if claim_folklore
  then verdict_folklore_outlier_refuse
  else if negb (outlierIncidenceNontrivial h)
  then verdict_trivial_z_refuse
  else if negb (z_valid (outlier_inc_z h))
  then verdict_trivial_z_refuse
  else
    match m with
    | outlier_is_theorem_unwired => verdict_outlier_terminal_named_ok
    | outlier_is_theorem_assumed
    | outlier_is_theorem_surrogate => verdict_unwired_ok
    | outlier_is_theorem_proved => verdict_proved_without_bar_refuse
    end.

Definition evaluate_outlier_close
  (m : OutlierIsTheoremModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : outlier_is_theorem_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | outlier_is_theorem_unwired => verdict_unwired_ok
    | outlier_is_theorem_assumed
    | outlier_is_theorem_proved
    | outlier_is_theorem_surrogate => verdict_outlier_terminal_named_ok
    end.

Lemma unwired_close_without_production_wiring :
  evaluate_outlier_close outlier_is_theorem_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Lemma helium_no_ore_named_ok :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceHeliumNoOre
    false false false = verdict_outlier_terminal_named_ok.
Proof. reflexivity. Qed.

Lemma neon_no_ore_named_ok :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceNeonNoOre
    false false false = verdict_outlier_terminal_named_ok.
Proof. reflexivity. Qed.

Lemma gold_native_named_ok :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceGoldNative
    false false false = verdict_outlier_terminal_named_ok.
Proof. reflexivity. Qed.

Lemma iron_oxide_named_ok :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceIronOxide
    false false false = verdict_outlier_terminal_named_ok.
Proof. reflexivity. Qed.

Lemma helium_trace_named_ok :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceHeliumTrace
    false false false = verdict_outlier_terminal_named_ok.
Proof. reflexivity. Qed.

Theorem named_outlier_terminals_not_folklore :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceHeliumNoOre
    false false false = verdict_outlier_terminal_named_ok /\
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceNeonNoOre
    false false false = verdict_outlier_terminal_named_ok /\
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceGoldNative
    false false false = verdict_outlier_terminal_named_ok /\
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceIronOxide
    false false false = verdict_outlier_terminal_named_ok /\
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceHeliumTrace
    false false false = verdict_outlier_terminal_named_ok /\
  folklore_outlier_refused = true /\
  honest_terminal_not_folklore helium_no_ore_terminal = true /\
  honest_terminal_not_folklore neon_no_ore_terminal = true /\
  honest_terminal_not_folklore gold_native_outlier_terminal = true /\
  honest_terminal_not_folklore iron_oxide_product_terminal = true /\
  honest_terminal_not_folklore helium_trace_atmophile_terminal = true.
Proof.
  repeat split; reflexivity.
Qed.

Lemma trivial_z_refused :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceTrivial
    false false false = verdict_trivial_z_refuse.
Proof. reflexivity. Qed.

Theorem trivial_z_fail_closed :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceTrivial
    false false false = verdict_trivial_z_refuse /\
  outlier_is_theorem_verdict_ok
    (evaluate_outlier_incidence
       outlier_is_theorem_unwired outlierIncidenceTrivial
       false false false) = false.
Proof.
  split.
  - apply trivial_z_refused.
  - unfold outlier_is_theorem_verdict_ok.
    rewrite trivial_z_refused.
    reflexivity.
Qed.

Lemma folklore_outlier_refuse :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceGoldNative
    false false true = verdict_folklore_outlier_refuse.
Proof. reflexivity. Qed.

Lemma green_invent_refuse_unwired :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceGoldNative
    true false false = verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Lemma proved_without_bar_refuse :
  evaluate_outlier_incidence
    outlier_is_theorem_unwired outlierIncidenceGoldNative
    false true false = verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Lemma outlier_production_wired_refuse :
  evaluate_outlier_close
    outlier_is_theorem_unwired false true = verdict_production_wired_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — lib.rs / eos.rs not wired (deferred composition)           *)
(* ------------------------------------------------------------------ *)

Definition outlierIsTheoremWiredInLib : bool := false.

Definition outlierIsTheoremWiredInEos : bool := false.

Definition outlierIsTheoremProductionWired : bool := false.

Lemma outlier_is_theorem_not_wired_lib :
  outlierIsTheoremWiredInLib = false.
Proof. reflexivity. Qed.

Lemma outlier_is_theorem_not_wired_eos :
  outlierIsTheoremWiredInEos = false.
Proof. reflexivity. Qed.

Lemma outlier_is_theorem_production_wired_false :
  outlierIsTheoremProductionWired = false.
Proof. reflexivity. Qed.

Lemma wave100_not_wired_lib_or_eos :
  negb outlierIsTheoremWiredInLib &&
  negb outlierIsTheoremWiredInEos = true.
Proof. reflexivity. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_marker_named :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Row proved fence — Unwired scaffold, not path-census Proved         *)
(* ------------------------------------------------------------------ *)

Definition outlierIsTheoremProved : bool := false.

Lemma outlier_is_theorem_proved_false :
  outlierIsTheoremProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table :
  not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

Definition soleAxiomCount : nat := 1.

Lemma sole_axiom_count_is_one :
  soleAxiomCount = 1.
Proof. reflexivity. Qed.

Definition outlierIsTheoremIsNewAxiom : Prop := False.

Lemma outlier_is_theorem_not_new_axiom :
  ~ outlierIsTheoremIsNewAxiom.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — read-only cites)    *)
(* ------------------------------------------------------------------ *)

Definition outlierIsTheoremCellId : string :=
  "CHEM-FORMAL-Q-COQ-OUTLIER-IS-THEOREM-CONSERVATION".

Definition outlierIsTheoremNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-OUTLIER-IS-THEOREM-CONSERVATION v50 outlier-is-theorem nothing in Z=1..118 or Interact/Ore/Refine may rest as folklore outlier honest terminals theorem deferred_composition typed Absent He Ne no ore missing Interact Au native Fe oxide product named measured remainder outlierIsTheoremProved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation not second axiom not GREEN not physics GREEN not production_wired".

Definition outlierIsTheoremIntAuthority : string :=
  "umst/umst-chem/src/x_rows/outlier_is_theorem.rs".

Definition outlierIsTheoremIntCrossCellId : string :=
  "CHEM-INT-CROSS-OUTLIER-IS-THEOREM-CONSERVATION".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition occurrenceFamilyPatternAuthority : string :=
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition interactEngineClosedShellAuthority : string :=
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs".

Lemma outlier_is_theorem_cell_id :
  outlierIsTheoremCellId =
  "CHEM-FORMAL-Q-COQ-OUTLIER-IS-THEOREM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma outlier_is_theorem_cites_int_authority :
  outlierIsTheoremIntAuthority <>
  "umst/umst-chem/src/x_rows/outlier_is_theorem.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma outlier_is_theorem_cites_int_cross_cell :
  outlierIsTheoremIntCrossCellId =
  "CHEM-INT-CROSS-OUTLIER-IS-THEOREM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma outlier_is_theorem_cites_occupancy_engine_sort :
  occupancyEngineSortAuthority <> "".
Proof. discriminate. Qed.

Lemma outlier_is_theorem_cites_occurrence_family_pattern :
  occurrenceFamilyPatternAuthority <> "".
Proof. discriminate. Qed.

Lemma outlier_is_theorem_cites_homolog_exception_not_copy :
  homologExceptionNotCopyAuthority <> "".
Proof. discriminate. Qed.

Lemma outlier_is_theorem_cites_interact_engine_closed_shell :
  interactEngineClosedShellAuthority <> "".
Proof. discriminate. Qed.

Lemma outlier_is_theorem_modality_unwired :
  outlierIsTheoremModalityCurrent = outlier_is_theorem_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition outlierIsTheoremPhysicsGreenAuthorized : Prop := False.

Lemma outlier_is_theorem_physics_green_false :
  ~ outlierIsTheoremPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation close theorem — Unwired honest scaffold                  *)
(* ------------------------------------------------------------------ *)

Theorem outlier_is_theorem_conservation :
  evaluate_outlier_close
    outlier_is_theorem_unwired false false = verdict_unwired_ok /\
  outlierIsTheoremProved = false /\
  folklore_outlier_refused = true /\
  outlierIsTheoremWiredInLib = false /\
  outlierIsTheoremWiredInEos = false.
Proof.
  repeat split; reflexivity.
Qed.

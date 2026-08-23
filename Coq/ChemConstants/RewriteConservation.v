(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: RewriteConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: FP-03 thermo-preserving rewrite conservation.    *)
(*  Fusion of admissible rewrites typed; thermo-preserving fusion        *)
(*  identity conserved; non-preserving steps fail-closed. Modality       *)
(*  Unwired; fp03RewriteProved Unwired not Proved. Geometry routes       *)
(*  knowing/quantum fiber not meso acting. Not 118² GREEN table.         *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +         *)
(*  conservation framing — rewrite conservation is not a second axiom.   *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  FP-03 rewrite conservation modality (Unwired / Assumed /            *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive RewriteConservationModality : Type :=
  | rewrite_conservation_unwired
  | rewrite_conservation_assumed
  | rewrite_conservation_proved
  | rewrite_conservation_surrogate.

Definition rewriteConservationModalityCurrent : RewriteConservationModality :=
  rewrite_conservation_unwired.

Definition rewrite_lattice_cardinality : nat := 4.

Lemma rewrite_lattice_cardinality_is_four :
  rewrite_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma rewrite_lattice_not_118_squared :
  negb (Nat.eqb rewrite_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold rewrite_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  ThermoInvariant — mass / energy / entropy under single axiom         *)
(* ------------------------------------------------------------------ *)

Inductive thermo_invariant : Type :=
  | invariant_mass_conservation
  | invariant_energy_balance
  | invariant_entropy_non_decrease.

Definition thermo_invariant_count : nat := 3.

Lemma thermo_invariant_count_is_three :
  thermo_invariant_count = 3.
Proof. reflexivity. Qed.

Definition thermo_invariant_all : list thermo_invariant :=
  [invariant_mass_conservation;
   invariant_energy_balance;
   invariant_entropy_non_decrease].

Lemma thermo_invariant_all_length :
  length thermo_invariant_all = thermo_invariant_count.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ThermoRewriteWitness — design scaffold (not live solver)            *)
(* ------------------------------------------------------------------ *)

Record thermo_rewrite_witness : Type := {
  mass_delta_milli : nat;
  energy_delta_microj : nat;
  entropy_delta_milli : Z;
  external_work_microj : nat
}.

Definition thermoRewriteWitnessBalanced : thermo_rewrite_witness :=
  {| mass_delta_milli := 0;
     energy_delta_microj := 0;
     entropy_delta_milli := 0%Z;
     external_work_microj := 0 |}.

Definition thermoRewriteWitnessMassViolate : thermo_rewrite_witness :=
  {| mass_delta_milli := 1;
     energy_delta_microj := 0;
     entropy_delta_milli := 0%Z;
     external_work_microj := 0 |}.

Definition thermoRewriteWitnessSecondLawViolate : thermo_rewrite_witness :=
  {| mass_delta_milli := 0;
     energy_delta_microj := 0;
     entropy_delta_milli := -1%Z;
     external_work_microj := 0 |}.

Lemma balanced_witness_mass_zero :
  thermoRewriteWitnessBalanced.(mass_delta_milli) = 0.
Proof. reflexivity. Qed.

Lemma balanced_witness_energy_zero :
  thermoRewriteWitnessBalanced.(energy_delta_microj) = 0.
Proof. reflexivity. Qed.

Lemma mass_violate_witness_mass_positive :
  0 < thermoRewriteWitnessMassViolate.(mass_delta_milli).
Proof. apply Nat.lt_0_succ. Qed.

Definition entropy_is_negative (z : Z) : bool :=
  match z with
  | Zpos _ => false
  | Z0 => false
  | Zneg _ => true
  end.

Lemma second_law_violate_entropy_negative :
  entropy_is_negative
    (thermoRewriteWitnessSecondLawViolate.(entropy_delta_milli)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  ThermoPreservingVerdict — fail-closed close lattice                 *)
(* ------------------------------------------------------------------ *)

Inductive thermo_preserving_verdict : Type :=
  | verdict_design_ok
  | verdict_preserving_ok
  | verdict_fusion_ok
  | verdict_conservation_violate
  | verdict_second_law_violate
  | verdict_green_invent_refuse.

Definition thermo_preserving_verdict_ok (v : thermo_preserving_verdict) : bool :=
  match v with
  | verdict_design_ok => true
  | verdict_preserving_ok => true
  | verdict_fusion_ok => true
  | _ => false
  end.

Definition evaluate_thermo_witness
  (w : thermo_rewrite_witness) (claim_physics_green : bool)
  : thermo_preserving_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if Nat.ltb 0 w.(mass_delta_milli)
       || Nat.ltb 0 w.(energy_delta_microj)
  then verdict_conservation_violate
  else if entropy_is_negative w.(entropy_delta_milli)
       then if negb (Nat.ltb 0 w.(external_work_microj))
            then verdict_second_law_violate
            else verdict_preserving_ok
       else verdict_preserving_ok.

Lemma balanced_witness_preserving_ok :
  evaluate_thermo_witness thermoRewriteWitnessBalanced false =
  verdict_preserving_ok.
Proof. reflexivity. Qed.

Theorem balanced_witness_preserving :
  evaluate_thermo_witness thermoRewriteWitnessBalanced false =
  verdict_preserving_ok /\
  thermo_preserving_verdict_ok
    (evaluate_thermo_witness thermoRewriteWitnessBalanced false) = true.
Proof.
  split.
  - apply balanced_witness_preserving_ok.
  - unfold thermo_preserving_verdict_ok.
    rewrite balanced_witness_preserving_ok.
    reflexivity.
Qed.

Lemma mass_violate_refused :
  evaluate_thermo_witness thermoRewriteWitnessMassViolate false =
  verdict_conservation_violate.
Proof. reflexivity. Qed.

Theorem conservation_violate_fail_closed :
  evaluate_thermo_witness thermoRewriteWitnessMassViolate false =
  verdict_conservation_violate /\
  thermo_preserving_verdict_ok
    (evaluate_thermo_witness thermoRewriteWitnessMassViolate false) = false.
Proof.
  split.
  - apply mass_violate_refused.
  - unfold thermo_preserving_verdict_ok.
    rewrite mass_violate_refused.
    reflexivity.
Qed.

Lemma second_law_violate_refused :
  evaluate_thermo_witness thermoRewriteWitnessSecondLawViolate false =
  verdict_second_law_violate.
Proof. reflexivity. Qed.

Theorem second_law_violate_fail_closed :
  evaluate_thermo_witness thermoRewriteWitnessSecondLawViolate false =
  verdict_second_law_violate /\
  thermo_preserving_verdict_ok
    (evaluate_thermo_witness thermoRewriteWitnessSecondLawViolate false) = false.
Proof.
  split.
  - apply second_law_violate_refused.
  - unfold thermo_preserving_verdict_ok.
    rewrite second_law_violate_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  ThermoRewriteStep — tagged rewrite classifier scaffold              *)
(* ------------------------------------------------------------------ *)

Inductive thermo_rewrite_step : Type :=
  | rewrite_step_identity
  | rewrite_step_admissible
  | rewrite_step_conservation_violate
  | rewrite_step_second_law_violate.

Definition thermo_rewrite_step_preserving (s : thermo_rewrite_step) : bool :=
  match s with
  | rewrite_step_identity => true
  | rewrite_step_admissible => true
  | rewrite_step_conservation_violate => false
  | rewrite_step_second_law_violate => false
  end.

Lemma identity_step_preserving :
  thermo_rewrite_step_preserving rewrite_step_identity = true.
Proof. reflexivity. Qed.

Lemma admissible_step_preserving :
  thermo_rewrite_step_preserving rewrite_step_admissible = true.
Proof. reflexivity. Qed.

Lemma conservation_violate_step_not_preserving :
  thermo_rewrite_step_preserving rewrite_step_conservation_violate = false.
Proof. reflexivity. Qed.

Lemma second_law_violate_step_not_preserving :
  thermo_rewrite_step_preserving rewrite_step_second_law_violate = false.
Proof. reflexivity. Qed.

Definition witness_is_identity (w : thermo_rewrite_witness) : bool :=
  Nat.eqb w.(mass_delta_milli) 0 &&
  Nat.eqb w.(energy_delta_microj) 0 &&
  negb (entropy_is_negative w.(entropy_delta_milli)) &&
  Nat.eqb w.(external_work_microj) 0.

Definition classify_rewrite_step (w : thermo_rewrite_witness) : thermo_rewrite_step :=
  match evaluate_thermo_witness w false with
  | verdict_preserving_ok =>
      if witness_is_identity w then rewrite_step_identity else rewrite_step_admissible
  | verdict_conservation_violate => rewrite_step_conservation_violate
  | verdict_second_law_violate => rewrite_step_second_law_violate
  | _ => rewrite_step_conservation_violate
  end.

Lemma classify_balanced_is_identity :
  classify_rewrite_step thermoRewriteWitnessBalanced = rewrite_step_identity.
Proof. reflexivity. Qed.

Lemma classify_mass_violate_is_conservation_violate :
  classify_rewrite_step thermoRewriteWitnessMassViolate =
  rewrite_step_conservation_violate.
Proof. reflexivity. Qed.

Lemma classify_second_law_violate :
  classify_rewrite_step thermoRewriteWitnessSecondLawViolate =
  rewrite_step_second_law_violate.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  FusedThermoRewrite — FP-03 fusion law preview                       *)
(* ------------------------------------------------------------------ *)

Inductive fused_thermo_rewrite : Type :=
  | fused_rewrite_identity
  | fused_rewrite_sequential (first second : thermo_rewrite_step).

Definition thermo_rewrite_step_beq (s1 s2 : thermo_rewrite_step) : bool :=
  match s1, s2 with
  | rewrite_step_identity, rewrite_step_identity => true
  | rewrite_step_admissible, rewrite_step_admissible => true
  | rewrite_step_conservation_violate, rewrite_step_conservation_violate => true
  | rewrite_step_second_law_violate, rewrite_step_second_law_violate => true
  | _, _ => false
  end.

Definition fuse_rewrite_steps
  (first second : thermo_rewrite_step) : fused_thermo_rewrite :=
  if thermo_rewrite_step_beq first rewrite_step_identity &&
     thermo_rewrite_step_beq second rewrite_step_identity
  then fused_rewrite_identity
  else fused_rewrite_sequential first second.

Definition fuse_rewrite_steps_direct
  (first second : thermo_rewrite_step) : fused_thermo_rewrite :=
  fuse_rewrite_steps first second.

Lemma fuse_identity_identity :
  fuse_rewrite_steps_direct rewrite_step_identity rewrite_step_identity =
  fused_rewrite_identity.
Proof. reflexivity. Qed.

Lemma fuse_admissible_identity :
  fuse_rewrite_steps_direct rewrite_step_admissible rewrite_step_identity =
  fused_rewrite_sequential rewrite_step_admissible rewrite_step_identity.
Proof. reflexivity. Qed.

Definition evaluate_fused_rewrite
  (fused : fused_thermo_rewrite) (claim_physics_green : bool)
  : thermo_preserving_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else
    match fused with
    | fused_rewrite_identity => verdict_fusion_ok
    | fused_rewrite_sequential first second =>
        if negb (thermo_rewrite_step_preserving first)
        then
          match first with
          | rewrite_step_conservation_violate => verdict_conservation_violate
          | rewrite_step_second_law_violate => verdict_second_law_violate
          | _ => verdict_design_ok
          end
        else if negb (thermo_rewrite_step_preserving second)
        then
          match second with
          | rewrite_step_conservation_violate => verdict_conservation_violate
          | rewrite_step_second_law_violate => verdict_second_law_violate
          | _ => verdict_design_ok
          end
        else verdict_fusion_ok
    end.

Lemma fused_identity_ok :
  evaluate_fused_rewrite fused_rewrite_identity false = verdict_fusion_ok.
Proof. reflexivity. Qed.

Theorem thermo_preserving_fusion_identity_conserved :
  fuse_rewrite_steps_direct rewrite_step_identity rewrite_step_identity =
  fused_rewrite_identity /\
  evaluate_fused_rewrite fused_rewrite_identity false = verdict_fusion_ok.
Proof.
  split.
  - apply fuse_identity_identity.
  - apply fused_identity_ok.
Qed.

Lemma fusion_preserving_admissible_identity_ok :
  evaluate_fused_rewrite
    (fuse_rewrite_steps_direct rewrite_step_admissible rewrite_step_identity)
    false =
  verdict_fusion_ok.
Proof. reflexivity. Qed.

Theorem fusion_preserving_steps_admits :
  thermo_rewrite_step_preserving rewrite_step_admissible = true /\
  thermo_rewrite_step_preserving rewrite_step_identity = true /\
  evaluate_fused_rewrite
    (fuse_rewrite_steps_direct rewrite_step_admissible rewrite_step_identity)
    false =
  verdict_fusion_ok.
Proof.
  repeat split; reflexivity.
Qed.

Lemma fused_conservation_violate_refused :
  evaluate_fused_rewrite
    (fused_rewrite_sequential rewrite_step_conservation_violate
       rewrite_step_identity)
    false =
  verdict_conservation_violate.
Proof. reflexivity. Qed.

Theorem non_preserving_step_fail_closed :
  evaluate_fused_rewrite
    (fused_rewrite_sequential rewrite_step_conservation_violate
       rewrite_step_identity)
    false =
  verdict_conservation_violate /\
  thermo_preserving_verdict_ok
    (evaluate_fused_rewrite
       (fused_rewrite_sequential rewrite_step_conservation_violate
          rewrite_step_identity)
       false) =
  false.
Proof.
  split.
  - apply fused_conservation_violate_refused.
  - unfold thermo_preserving_verdict_ok.
    rewrite fused_conservation_violate_refused.
    reflexivity.
Qed.

Lemma fused_second_law_violate_refused :
  evaluate_fused_rewrite
    (fused_rewrite_sequential rewrite_step_identity
       rewrite_step_second_law_violate)
    false =
  verdict_second_law_violate.
Proof. reflexivity. Qed.

Theorem non_preserving_second_law_step_fail_closed :
  evaluate_fused_rewrite
    (fused_rewrite_sequential rewrite_step_identity
       rewrite_step_second_law_violate)
    false =
  verdict_second_law_violate /\
  thermo_preserving_verdict_ok
    (evaluate_fused_rewrite
       (fused_rewrite_sequential rewrite_step_identity
          rewrite_step_second_law_violate)
       false) =
  false.
Proof.
  split.
  - apply fused_second_law_violate_refused.
  - unfold thermo_preserving_verdict_ok.
    rewrite fused_second_law_violate_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Rewrite conservation close verdict — fail-closed lattice            *)
(* ------------------------------------------------------------------ *)

Inductive rewrite_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_fusion_identity_ok
  | verdict_non_preserving_refuse
  | verdict_rewrite_green_invent_refuse
  | verdict_production_wired_refuse.

Definition rewrite_conservation_verdict_ok (v : rewrite_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_fusion_identity_ok => true
  | _ => false
  end.

Definition rewrite_conservation_verdict_beq
  (v1 v2 : rewrite_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_fusion_identity_ok, verdict_fusion_identity_ok => true
  | verdict_non_preserving_refuse, verdict_non_preserving_refuse => true
  | verdict_rewrite_green_invent_refuse, verdict_rewrite_green_invent_refuse => true
  | verdict_production_wired_refuse, verdict_production_wired_refuse => true
  | _, _ => false
  end.

Definition evaluate_rewrite_conservation_close
  (m : RewriteConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : rewrite_conservation_verdict :=
  if claim_physics_green
  then verdict_rewrite_green_invent_refuse
  else if claim_production_wired
  then verdict_production_wired_refuse
  else
    match m with
    | rewrite_conservation_unwired => verdict_unwired_ok
    | rewrite_conservation_assumed
    | rewrite_conservation_proved
    | rewrite_conservation_surrogate => verdict_fusion_identity_ok
    end.

Definition rewrite_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_rewrite_conservation_close
          rewrite_conservation_proved claim_physics_green claim_production_wired with
  | verdict_fusion_identity_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Rewrite conservation law cells — four laws, open @ Unwired            *)
(* ------------------------------------------------------------------ *)

Inductive rewrite_conservation_law : Type :=
  | law_fusion_identity
  | law_non_preserving_refuse
  | law_green_invent_refuse
  | law_production_wired_refuse.

Definition rewrite_conservation_law_count : nat := 4.

Lemma rewrite_conservation_law_count_is_four :
  rewrite_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive rewrite_conservation_law_witness : Type :=
  | rewrite_law_witness_open
  | rewrite_law_witness_proved.

Definition evaluate_rewrite_conservation_law_witness
  (law : rewrite_conservation_law) (m : RewriteConservationModality)
  : rewrite_conservation_law_witness :=
  match m with
  | rewrite_conservation_unwired
  | rewrite_conservation_assumed
  | rewrite_conservation_surrogate => rewrite_law_witness_open
  | rewrite_conservation_proved => rewrite_law_witness_proved
  end.

Lemma all_rewrite_conservation_laws_open_at_unwired :
  evaluate_rewrite_conservation_law_witness law_fusion_identity
    rewrite_conservation_unwired = rewrite_law_witness_open /\
  evaluate_rewrite_conservation_law_witness law_non_preserving_refuse
    rewrite_conservation_unwired = rewrite_law_witness_open /\
  evaluate_rewrite_conservation_law_witness law_green_invent_refuse
    rewrite_conservation_unwired = rewrite_law_witness_open /\
  evaluate_rewrite_conservation_law_witness law_production_wired_refuse
    rewrite_conservation_unwired = rewrite_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  FP-03 pins (structure witnesses — rewrite laws not Proved)        *)
(* ------------------------------------------------------------------ *)

Definition fp03RewriteProved : bool := false.

Lemma fp03_rewrite_proved_false : fp03RewriteProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_rewrite_conservation_close
    rewrite_conservation_unwired false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_rewrite_conservation_close
    rewrite_conservation_unwired false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  rewrite_conservation_verdict_ok
    (evaluate_rewrite_conservation_close
       rewrite_conservation_unwired false false) =
  true.
Proof.
  unfold rewrite_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fusion identity close — thermo-preserving fusion conserved          *)
(* ------------------------------------------------------------------ *)

Lemma fusion_identity_close_ok :
  evaluate_rewrite_conservation_close
    rewrite_conservation_proved false false =
  verdict_fusion_identity_ok.
Proof. reflexivity. Qed.

Theorem thermo_preserving_fusion_identity_conservation_close :
  evaluate_rewrite_conservation_close
    rewrite_conservation_proved false false =
  verdict_fusion_identity_ok /\
  rewrite_conservation_authorized false false = true.
Proof.
  split.
  - apply fusion_identity_close_ok.
  - unfold rewrite_conservation_authorized.
    rewrite fusion_identity_close_ok.
    reflexivity.
Qed.

Lemma fusion_identity_verdict_ok :
  rewrite_conservation_verdict_ok
    (evaluate_rewrite_conservation_close
       rewrite_conservation_proved false false) =
  true.
Proof.
  unfold rewrite_conservation_verdict_ok.
  rewrite fusion_identity_close_ok.
  reflexivity.
Qed.

Lemma fusion_identity_still_not_fp03_proved :
  rewrite_conservation_verdict_ok
    (evaluate_rewrite_conservation_close
       rewrite_conservation_proved false false) =
  true /\
  fp03RewriteProved = false.
Proof.
  split.
  - apply fusion_identity_verdict_ok.
  - apply fp03_rewrite_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_rewrite_conservation_close
    rewrite_conservation_unwired true false =
  verdict_rewrite_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  rewrite_conservation_verdict_ok
    (evaluate_rewrite_conservation_close
       rewrite_conservation_unwired true false) =
  false.
Proof.
  unfold rewrite_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_witness_refuse :
  evaluate_thermo_witness thermoRewriteWitnessBalanced true =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — rewrite lattice not production wired      *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_rewrite_conservation_close
    rewrite_conservation_proved false true =
  verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  rewrite_conservation_verdict_ok
    (evaluate_rewrite_conservation_close
       rewrite_conservation_proved false true) =
  false.
Proof.
  unfold rewrite_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Rewrite conservation coherence scaffold — fixture witnesses         *)
(* ------------------------------------------------------------------ *)

Definition rewrite_conservation_coherence_scaffold : bool :=
  rewrite_conservation_verdict_beq
    (evaluate_rewrite_conservation_close
       rewrite_conservation_proved false false)
    verdict_fusion_identity_ok &&
  rewrite_conservation_verdict_beq
    (evaluate_rewrite_conservation_close
       rewrite_conservation_unwired true false)
    verdict_rewrite_green_invent_refuse &&
  rewrite_conservation_verdict_beq
    (evaluate_rewrite_conservation_close
       rewrite_conservation_proved false true)
    verdict_production_wired_refuse.

Lemma rewrite_conservation_coherence_scaffold_true :
  rewrite_conservation_coherence_scaffold = true.
Proof.
  unfold rewrite_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem rewrite_conservation_coherence_scaffold_theorem :
  evaluate_rewrite_conservation_close
    rewrite_conservation_proved false false =
    verdict_fusion_identity_ok /\
  evaluate_rewrite_conservation_close
    rewrite_conservation_unwired true false =
    verdict_rewrite_green_invent_refuse /\
  evaluate_rewrite_conservation_close
    rewrite_conservation_proved false true =
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
  | claim_rewrite_conservation.

Definition rewrite_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition rewrite_conservation_knowing_fiber_ok : bool :=
  rewrite_conservation_fiber_ok fiber_quantum_knowing.

Definition rewrite_conservation_meso_acting_ok : bool :=
  rewrite_conservation_fiber_ok fiber_meso_acting.

Lemma rewrite_conservation_knowing_fiber_ok_true :
  rewrite_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma rewrite_conservation_meso_acting_not_ok :
  rewrite_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem rewrite_conservation_routes_knowing_not_meso :
  rewrite_conservation_knowing_fiber_ok = true /\
  rewrite_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply rewrite_conservation_knowing_fiber_ok_true.
  - apply rewrite_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  rewrite_conservation_knowing_fiber_ok &&
  negb rewrite_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, rewrite_conservation_knowing_fiber_ok,
    rewrite_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — fusion identity + fail-closed + fiber + FP-03  *)
(* ------------------------------------------------------------------ *)

Theorem rewrite_conservation_fixture_scaffold :
  fuse_rewrite_steps_direct rewrite_step_identity rewrite_step_identity =
    fused_rewrite_identity /\
  evaluate_fused_rewrite fused_rewrite_identity false = verdict_fusion_ok /\
  evaluate_thermo_witness thermoRewriteWitnessMassViolate false =
    verdict_conservation_violate /\
  evaluate_rewrite_conservation_close
    rewrite_conservation_unwired false false =
    verdict_unwired_ok /\
  rewrite_conservation_knowing_fiber_ok = true /\
  rewrite_conservation_meso_acting_ok = false /\
  fp03RewriteProved = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — rewrite conservation) *)
(* ------------------------------------------------------------------ *)

Definition thermoPreservingRewriteAuthority : string :=
  "umst/umst-chem/src/thermo_preserving_rewrite.rs".

Definition chemIntProveFp03RewriteAuthority : string :=
  "CHEM-INT-PROVE-FP-03-REWRITE".

Definition thermoPreservingRewriteMarker : string :=
  "chem_l0_thermo_preserving_rewrite_v1".

Definition rewriteConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-REWRITE-CONSERVATION".

Definition rewriteConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-REWRITE-CONSERVATION FP-03 thermo-preserving rewrite conservation fusion identity conserved non-preserving fail-closed fp03RewriteProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second rewrite axiom not GREEN DFT not physics GREEN not production_wired".

Lemma rewrite_conservation_cell_id :
  rewriteConservationCellId = "CHEM-FORMAL-Q-COQ-REWRITE-CONSERVATION".
Proof. reflexivity. Qed.

Lemma rewrite_conservation_cites_thermo_preserving_rewrite_rs :
  thermoPreservingRewriteAuthority <> "".
Proof. discriminate. Qed.

Lemma rewrite_conservation_cites_int_prove_fp_03_rewrite :
  chemIntProveFp03RewriteAuthority = "CHEM-INT-PROVE-FP-03-REWRITE".
Proof. reflexivity. Qed.

Lemma rewrite_conservation_cites_marker :
  thermoPreservingRewriteMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second rewrite axiom *)
(* ------------------------------------------------------------------ *)

Definition rewriteSecondLawConservationFraming : string :=
  "second_law_conservation_rewrite_one_axiom_not_second_rewrite_axiom".

Lemma rewrite_not_second_rewrite_axiom :
  rewriteSecondLawConservationFraming <> "second_rewrite_axiom".
Proof. discriminate. Qed.

Lemma rewrite_second_law_conservation_framing :
  rewriteSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma rewrite_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma rewrite_conservation_modality_unwired :
  rewriteConservationModalityCurrent = rewrite_conservation_unwired.
Proof. reflexivity. Qed.

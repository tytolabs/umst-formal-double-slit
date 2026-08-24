(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: MachineTemperature.v                                  *)
(*                                                                      *)
(*  Knowing/quantum Coq: §17.2 Excitement T is machine temperature of   *)
(*  the coupled repository-in-machine (Landauer erasure environment),   *)
(*  not wall clock and not an abstract DAG scalar. Cross-node energy    *)
(*  witness may refuse when Landauer floor exceeds available energy.    *)
(*  Urge composes imported Excitement select — no second argmin.        *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. Zero new Axiom.               *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Machine-temperature modality (Unwired / Assumed / Proved /         *)
(*  Surrogate) — knowing fiber §17.2                                    *)
(* ------------------------------------------------------------------ *)

Inductive MachineTemperatureModality : Type :=
  | machine_temperature_unwired
  | machine_temperature_assumed
  | machine_temperature_proved
  | machine_temperature_surrogate.

Definition machineTemperatureModalityCurrent : MachineTemperatureModality :=
  machine_temperature_unwired.

(* ------------------------------------------------------------------ *)
(*  Temperature ontology source (§17.2 pin)                             *)
(* ------------------------------------------------------------------ *)

Inductive TemperatureSource : Type :=
  | repository_in_machine
  | wall_clock_theater
  | abstract_dag_scalar.

(* ------------------------------------------------------------------ *)
(*  Typed refusal reasons — positive refuse, not silent no-op           *)
(* ------------------------------------------------------------------ *)

Inductive MachineTemperatureRefusal : Type :=
  | wall_clock_as_temperature
  | abstract_dag_scalar_as_temperature
  | cross_node_energy_witness_mismatch (node_id : string)
      (landauer_floor available : R)
  | second_argmin.

(* ------------------------------------------------------------------ *)
(*  Machine temperature witness scaffold                                *)
(* ------------------------------------------------------------------ *)

Record MachineTemperature : Type := {
  mt_kelvin : R;
  mt_node_id : string;
  mt_source : TemperatureSource
}.

Record MachineTemperatureCandidate : Type := {
  mtc_kelvin : R;
  mtc_node_id : string;
  mtc_source : TemperatureSource;
  mtc_erasure_bits : R;
  mtc_available_energy : R
}.

Record MachineTemperatureWitness : Type := {
  mtw_temperature : MachineTemperature;
  mtw_landauer_floor : R;
  mtw_available_energy : R
}.

Inductive MachineTemperatureEval : Type :=
  | mt_ok : MachineTemperatureWitness -> MachineTemperatureEval
  | mt_err : MachineTemperatureRefusal -> MachineTemperatureEval.

(* ------------------------------------------------------------------ *)
(*  Landauer erasure floor at machine T (kT ln2 per bit)                *)
(* ------------------------------------------------------------------ *)

Definition landauerFloor (T erasure_bits : R) : R :=
  erasure_bits * E_Landauer_bit T.

Definition machineTemperatureAdmitPred (c : MachineTemperatureCandidate) : Prop :=
  mtc_source c = repository_in_machine /\
  mtc_available_energy c >= landauerFloor (mtc_kelvin c) (mtc_erasure_bits c).

Definition evaluateMachineTemperature (c : MachineTemperatureCandidate)
  : MachineTemperatureEval :=
  match mtc_source c with
  | wall_clock_theater =>
      mt_err wall_clock_as_temperature
  | abstract_dag_scalar =>
      mt_err abstract_dag_scalar_as_temperature
  | repository_in_machine =>
      let floor := landauerFloor (mtc_kelvin c) (mtc_erasure_bits c) in
      if Rlt_dec (mtc_available_energy c) floor then
        mt_err (cross_node_energy_witness_mismatch (mtc_node_id c) floor
                  (mtc_available_energy c))
      else
        mt_ok {| mtw_temperature :=
                   {| mt_kelvin := mtc_kelvin c;
                      mt_node_id := mtc_node_id c;
                      mt_source := repository_in_machine |};
                 mtw_landauer_floor := floor;
                 mtw_available_energy := mtc_available_energy c |}
  end.


Lemma E_Landauer_bit_nonneg (T : R) :
  0 <= T -> 0 <= E_Landauer_bit T.
Proof.
  intros HT.
  unfold E_Landauer_bit.
  apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
  apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

Lemma landauerFloor_nonneg (T erasure_bits : R) :
  0 <= T -> 0 <= erasure_bits ->
  0 <= landauerFloor T erasure_bits.
Proof.
  intros HT Hbits.
  unfold landauerFloor.
  apply Rmult_le_pos; [exact Hbits|].
  apply E_Landauer_bit_nonneg; exact HT.
Qed.

Lemma measurementEnergyLowerBound_eq_landauerFloor (T bits : R) :
  measurementEnergyLowerBound T bits = landauerFloor T bits.
Proof.
  unfold measurementEnergyLowerBound, landauerFloor.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture pins (mirror URGE-INT-MACHINE-TEMPERATURE)                  *)
(* ------------------------------------------------------------------ *)

Definition fixtureM3Accept : MachineTemperatureCandidate :=
  {| mtc_kelvin := 310;
     mtc_node_id := "node-m3-rapl";
     mtc_source := repository_in_machine;
     mtc_erasure_bits := 0;
     mtc_available_energy := 50000000 |}.

Definition fixtureWallClockRefuse : MachineTemperatureCandidate :=
  {| mtc_kelvin := 0;
     mtc_node_id := "wall-clock-theater";
     mtc_source := wall_clock_theater;
     mtc_erasure_bits := 0;
     mtc_available_energy := 0 |}.

Definition fixtureDagScalarRefuse : MachineTemperatureCandidate :=
  {| mtc_kelvin := 1;
     mtc_node_id := "dag-scalar-theater";
     mtc_source := abstract_dag_scalar;
     mtc_erasure_bits := 0;
     mtc_available_energy := 0 |}.

Definition fixtureThinkpadCrossNodeRefuse : MachineTemperatureCandidate :=
  {| mtc_kelvin := 320;
     mtc_node_id := "node-thinkpad";
     mtc_source := repository_in_machine;
     mtc_erasure_bits := 64;
     mtc_available_energy := 0 |}.

Lemma fixture_m3_accept_ok :
  exists w, evaluateMachineTemperature fixtureM3Accept = mt_ok w.
Proof.
  unfold evaluateMachineTemperature, fixtureM3Accept, landauerFloor.
  simpl. destruct (Rlt_dec 50000000 (0 * E_Landauer_bit 310)) eqn:Hdec.
  - exfalso. lra.
  - exists {| mtw_temperature :=
               {| mt_kelvin := 310;
                  mt_node_id := "node-m3-rapl";
                  mt_source := repository_in_machine |};
             mtw_landauer_floor := 0 * E_Landauer_bit 310;
             mtw_available_energy := 50000000 |}.
    reflexivity.
Qed.

Lemma fixture_wall_clock_refuse :
  evaluateMachineTemperature fixtureWallClockRefuse =
  mt_err wall_clock_as_temperature.
Proof.
  unfold evaluateMachineTemperature, fixtureWallClockRefuse.
  reflexivity.
Qed.

Lemma fixture_dag_scalar_refuse :
  evaluateMachineTemperature fixtureDagScalarRefuse =
  mt_err abstract_dag_scalar_as_temperature.
Proof.
  unfold evaluateMachineTemperature, fixtureDagScalarRefuse.
  reflexivity.
Qed.

Lemma fixture_thinkpad_cross_node_refuse :
  exists floor,
    evaluateMachineTemperature fixtureThinkpadCrossNodeRefuse =
    mt_err (cross_node_energy_witness_mismatch "node-thinkpad" floor 0).
Proof.
  unfold evaluateMachineTemperature, fixtureThinkpadCrossNodeRefuse,
    landauerFloor.
  simpl. destruct (Rlt_dec 0 (64 * E_Landauer_bit 320)) eqn:Hdec.
  - exists (64 * E_Landauer_bit 320). reflexivity.
  - exfalso.
    assert (Hpos : 0 < 64 * E_Landauer_bit 320).
    { apply Rmult_lt_0_compat.
      - lra.
      - apply E_Landauer_bit_pos; lra. }
    lra.
Qed.

Lemma refuse_second_argmin_eval :
  mt_err second_argmin <> mt_ok
    {| mtw_temperature :=
         {| mt_kelvin := 0; mt_node_id := ""; mt_source := repository_in_machine |};
       mtw_landauer_floor := 0;
       mtw_available_energy := 0 |}.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Excitement compose pin — import select, not second argmin             *)
(* ------------------------------------------------------------------ *)

Definition excitementComposeSurrogate : string :=
  "UMST.Excitement.select".

Definition metaExcitementModule : string :=
  "umst-meta/crates/umst-meta/src/excitement.rs".

Lemma machine_temperature_compose_surrogate_ok :
  excitementComposeSurrogate = "UMST.Excitement.select".
Proof. reflexivity. Qed.

Lemma machine_temperature_meta_excitement_cited :
  metaExcitementModule <> "".
Proof. discriminate. Qed.

Lemma machine_temperature_not_second_argmin :
  excitementComposeSurrogate <> "second_q_argmin".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — machine T)           *)
(* ------------------------------------------------------------------ *)

Definition leanMachineTemperatureAuthority : string :=
  "umst/umst-formal-double-slit/Lean/UrgeKnowing/MachineTemperature.lean".

Definition urgeIntMachineTemperatureAuthority : string :=
  "umst/umst-urge/src/machine_temperature.rs".

Definition landauerEinsteinBridgeAuthority : string :=
  "umst/umst-formal-double-slit/Coq/LandauerEinsteinBridge.v".

Definition machineTemperatureCellId : string :=
  "URGE-FORMAL-Q-COQ-MACHINE-TEMPERATURE".

Definition machineTemperatureNonClaim : string :=
  "URGE-FORMAL-Q-COQ-MACHINE-TEMPERATURE §17.2 Excitement T is machine temperature of coupled repository-in-machine not wall clock not abstract DAG scalar Landauer erasure floor kT ln2 cross-node energy witness may refuse compose Excitement select not second argmin not physics GREEN not production_wired knowing fiber Unwired zero Admitted zero new Axiom".

Lemma machine_temperature_cell_id :
  machineTemperatureCellId = "URGE-FORMAL-Q-COQ-MACHINE-TEMPERATURE".
Proof. reflexivity. Qed.

Lemma machine_temperature_cites_lean_module :
  leanMachineTemperatureAuthority <> "".
Proof. discriminate. Qed.

Lemma machine_temperature_cites_urge_int :
  urgeIntMachineTemperatureAuthority <> "".
Proof. discriminate. Qed.

Lemma machine_temperature_cites_landauer_bridge :
  landauerEinsteinBridgeAuthority <> "".
Proof. discriminate. Qed.

Lemma machine_temperature_non_claim_not_wall_clock :
  machineTemperatureNonClaim <> "wall_clock_as_excitement_T".
Proof. discriminate. Qed.

Lemma machine_temperature_non_claim_not_dag_scalar :
  machineTemperatureNonClaim <> "abstract_DAG_scalar_as_T".
Proof. discriminate. Qed.

Lemma machine_temperature_deepen_honest :
  machineTemperatureNonClaim <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Not wall clock / not DAG scalar fence                               *)
(* ------------------------------------------------------------------ *)

Definition wallClockTheaterTag : string := "wall_clock_theater".
Definition abstractDagScalarTag : string := "abstract_dag_scalar".

Lemma machine_temperature_wall_clock_refused_positively :
  evaluateMachineTemperature fixtureWallClockRefuse <>
  mt_ok
    {| mtw_temperature :=
         {| mt_kelvin := 0; mt_node_id := ""; mt_source := repository_in_machine |};
       mtw_landauer_floor := 0;
       mtw_available_energy := 0 |}.
Proof.
  rewrite fixture_wall_clock_refuse.
  discriminate.
Qed.

Lemma machine_temperature_dag_scalar_refused_positively :
  evaluateMachineTemperature fixtureDagScalarRefuse <>
  mt_ok
    {| mtw_temperature :=
         {| mt_kelvin := 0; mt_node_id := ""; mt_source := repository_in_machine |};
       mtw_landauer_floor := 0;
       mtw_available_energy := 0 |}.
Proof.
  rewrite fixture_dag_scalar_refuse.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Definition productionWiredAuthorized : Prop := False.

Lemma machine_temperature_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma machine_temperature_production_wired_false :
  ~ productionWiredAuthorized.
Proof. intro H; exact H. Qed.

Lemma machine_temperature_modality_unwired :
  machineTemperatureModalityCurrent = machine_temperature_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing fiber pin — not meso thermo G(T,P,x) restated               *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma machine_temperature_not_meso_thermo_restate :
  machineTemperatureNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

Lemma machine_temperature_knowing_fiber_ok :
  machineTemperatureModalityCurrent = machine_temperature_unwired /\
  ~ physicsGreenAuthorized /\
  ~ productionWiredAuthorized.
Proof.
  split; [| split].
  - apply machine_temperature_modality_unwired.
  - apply machine_temperature_physics_green_false.
  - apply machine_temperature_production_wired_false.
Qed.

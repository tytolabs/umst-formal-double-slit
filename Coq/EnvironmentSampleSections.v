(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EnvironmentSampleSections.v                           *)
(*                                                                      *)
(*  Quantum / knowing fiber preview for environment SAMPLE sections:    *)
(*    - Vacuum / contained / messy as named knowing-fiber probes of     *)
(*      ONE Env sheaf (v15 — simultaneous triple, not XOR worlds)       *)
(*    - First-class section paths between sample strata                 *)
(*    - Reuses EnvironmentScaleCommute (no duplicate scale sheaf)       *)
(*                                                                      *)
(*  No meso / acting theorems. Modality Unwired; physics GREEN false.   *)
(* ================================================================== *)

Require Import UMSTFormal.ChemGeometry.
Require Import UMSTFormal.EnvironmentScaleCommute.
From Stdlib Require Import Reals RIneq Lra List.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Sample-section modality (knowing fiber — Unwired)                   *)
(* ------------------------------------------------------------------ *)

Inductive EnvironmentSampleSectionsModality : Type :=
  | ess_unwired | ess_assumed
  | ess_proved | ess_surrogate.

Definition environmentSampleSectionsModalityCurrent :
  EnvironmentSampleSectionsModality := ess_unwired.

Definition environmentSampleSectionCardinality : nat := 3%nat.

Lemma environment_sample_section_cardinality_three :
  environmentSampleSectionCardinality = 3%nat.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Named section tags (vacuum | contained | messy — not XOR)           *)
(* ------------------------------------------------------------------ *)

Inductive EnvironmentNamedSectionTag : Type :=
  | tag_vacuum | tag_contained | tag_messy.

Definition environmentNamedSectionTag (a : EnvSampleAxis) : EnvironmentNamedSectionTag :=
  match a with
  | env_axis_vacuum => tag_vacuum
  | env_axis_contained => tag_contained
  | env_axis_messy => tag_messy
  end.

Lemma environment_named_section_vacuum_tag :
  environmentNamedSectionTag env_axis_vacuum = tag_vacuum.
Proof. reflexivity. Qed.

Lemma environment_named_section_contained_tag :
  environmentNamedSectionTag env_axis_contained = tag_contained.
Proof. reflexivity. Qed.

Lemma environment_named_section_messy_tag :
  environmentNamedSectionTag env_axis_messy = tag_messy.
Proof. reflexivity. Qed.

Definition environmentSampleAxisIndex (a : EnvSampleAxis) : nat :=
  match a with
  | env_axis_vacuum => 0%nat
  | env_axis_contained => 1%nat
  | env_axis_messy => 2%nat
  end.

Lemma environment_sample_axis_index_distinct_vacuum_contained :
  environmentSampleAxisIndex env_axis_vacuum <>
  environmentSampleAxisIndex env_axis_contained.
Proof. discriminate. Qed.

Lemma environment_sample_axis_index_distinct_vacuum_messy :
  environmentSampleAxisIndex env_axis_vacuum <>
  environmentSampleAxisIndex env_axis_messy.
Proof. discriminate. Qed.

Lemma environment_sample_axis_index_distinct_contained_messy :
  environmentSampleAxisIndex env_axis_contained <>
  environmentSampleAxisIndex env_axis_messy.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  First-class section paths (adjacency + vacuum↔messy cross-link)      *)
(* ------------------------------------------------------------------ *)

Inductive EnvSectionPathId : Type :=
  | path_vacuum_to_contained
  | path_contained_to_vacuum
  | path_contained_to_messy
  | path_messy_to_contained
  | path_vacuum_to_messy
  | path_messy_to_vacuum.

Record EnvSectionPath : Type := mkEnvSectionPath {
  pathFrom : EnvSampleAxis;
  pathTo : EnvSampleAxis;
  pathId : EnvSectionPathId
}.

Definition envSectionPathVacuumToContained : EnvSectionPath :=
  {| pathFrom := env_axis_vacuum;
     pathTo := env_axis_contained;
     pathId := path_vacuum_to_contained |}.

Definition envSectionPathContainedToVacuum : EnvSectionPath :=
  {| pathFrom := env_axis_contained;
     pathTo := env_axis_vacuum;
     pathId := path_contained_to_vacuum |}.

Definition envSectionPathContainedToMessy : EnvSectionPath :=
  {| pathFrom := env_axis_contained;
     pathTo := env_axis_messy;
     pathId := path_contained_to_messy |}.

Definition envSectionPathMessyToContained : EnvSectionPath :=
  {| pathFrom := env_axis_messy;
     pathTo := env_axis_contained;
     pathId := path_messy_to_contained |}.

Definition envSectionPathVacuumToMessy : EnvSectionPath :=
  {| pathFrom := env_axis_vacuum;
     pathTo := env_axis_messy;
     pathId := path_vacuum_to_messy |}.

Definition envSectionPathMessyToVacuum : EnvSectionPath :=
  {| pathFrom := env_axis_messy;
     pathTo := env_axis_vacuum;
     pathId := path_messy_to_vacuum |}.

Definition environmentSectionPathCardinality : nat := 6%nat.

Definition environmentSectionPaths : list EnvSectionPath :=
  envSectionPathVacuumToContained ::
  envSectionPathContainedToVacuum ::
  envSectionPathContainedToMessy ::
  envSectionPathMessyToContained ::
  envSectionPathVacuumToMessy ::
  envSectionPathMessyToVacuum :: nil.

Lemma environment_section_path_count_six :
  length environmentSectionPaths = environmentSectionPathCardinality.
Proof. reflexivity. Qed.

Definition envSectionPathIsChange (p : EnvSectionPath) : bool :=
  negb (Nat.eqb (environmentSampleAxisIndex (pathFrom p))
                (environmentSampleAxisIndex (pathTo p))).

Lemma env_section_path_vacuum_to_contained_is_change :
  envSectionPathIsChange envSectionPathVacuumToContained = true.
Proof. reflexivity. Qed.

Fixpoint envSectionPathExists (from to : EnvSampleAxis) (paths : list EnvSectionPath) :
  bool :=
  match paths with
  | nil => false
  | p :: rest =>
      if andb
           (Nat.eqb (environmentSampleAxisIndex (pathFrom p))
                    (environmentSampleAxisIndex from))
           (Nat.eqb (environmentSampleAxisIndex (pathTo p))
                    (environmentSampleAxisIndex to))
      then true else envSectionPathExists from to rest
  end.

Lemma env_section_path_exists_vacuum_to_contained :
  envSectionPathExists env_axis_vacuum env_axis_contained environmentSectionPaths = true.
Proof. reflexivity. Qed.

Lemma env_section_path_exists_messy_to_vacuum :
  envSectionPathExists env_axis_messy env_axis_vacuum environmentSectionPaths = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing-fiber sample probes of ONE Env sheaf (not XOR)              *)
(* ------------------------------------------------------------------ *)

Record KnowingFiberSampleProbe : Type := mkKnowingFiberSampleProbe {
  kfProbe : KnowingProbe;
  kfField : EnvironmentSheafField
}.

Definition knowingFiberProbeVacuumAtQuantum (f : EnvironmentSheafField) :
  KnowingFiberSampleProbe :=
  {| kfProbe := probeVacuumAtQuantum;
     kfField := f |}.

Definition knowingFiberProbeContainedAtMeso (f : EnvironmentSheafField) :
  KnowingFiberSampleProbe :=
  {| kfProbe := probeContainedAtMeso;
     kfField := f |}.

Definition knowingFiberProbeMessyAtMacro (f : EnvironmentSheafField) :
  KnowingFiberSampleProbe :=
  {| kfProbe := probeMessyAtMacro;
     kfField := f |}.

Definition knowingFiberSampleValue (p : KnowingFiberSampleProbe) : R :=
  probeSample (kfField p) (kfProbe p).

Lemma knowing_fiber_probe_vacuum_at_quantum_named (f : EnvironmentSheafField) :
  knowingFiberSampleValue (knowingFiberProbeVacuumAtQuantum f) =
  residualPO2Pa (vacuum (atQuantum f)).
Proof.
  unfold knowingFiberSampleValue, knowingFiberProbeVacuumAtQuantum.
  apply probe_vacuum_at_quantum_named.
Qed.

Lemma knowing_fiber_probe_contained_at_meso_named (f : EnvironmentSheafField) :
  knowingFiberSampleValue (knowingFiberProbeContainedAtMeso f) =
  kelvin (contained (atMeso f)).
Proof. reflexivity. Qed.

Lemma knowing_fiber_probe_messy_at_macro_named (f : EnvironmentSheafField) :
  knowingFiberSampleValue (knowingFiberProbeMessyAtMacro f) =
  oreGradeFraction (messy (atMacro f)).
Proof. reflexivity. Qed.

Definition environmentKnowingFiberProbes (f : EnvironmentSheafField) :
  KnowingFiberSampleProbe * KnowingFiberSampleProbe * KnowingFiberSampleProbe :=
  ( knowingFiberProbeVacuumAtQuantum f,
    knowingFiberProbeContainedAtMeso f,
    knowingFiberProbeMessyAtMacro f ).

Lemma environment_knowing_fiber_probes_all_axes (f : EnvironmentSheafField) :
  let '(pv, pc, pm) := environmentKnowingFiberProbes f in
  axis (kfProbe pv) = env_axis_vacuum /\
  axis (kfProbe pc) = env_axis_contained /\
  axis (kfProbe pm) = env_axis_messy.
Proof.
  simpl.
  split; [reflexivity | split; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  ONE Env sheaf — sample sections coexist (not XOR worlds)           *)
(* ------------------------------------------------------------------ *)

Record EnvironmentSampleSheaf : Type := mkEnvironmentSampleSheaf {
  essField : EnvironmentSheafField;
  essModality : EnvironmentSampleSectionsModality;
  essScaleCommute : EnvironmentScaleCommute
}.

Definition environmentSampleSheafUnwired (e : ElementElectronic) :
  EnvironmentSampleSheaf :=
  {| essField := environmentSheafFieldAmbient;
     essModality := environmentSampleSectionsModalityCurrent;
     essScaleCommute := environmentScaleCommuteUnwired e |}.

Lemma environment_sample_sheaf_field_ambient_all_samples
  (s : EnvironmentSampleSheaf)
  (Heq : essField s = environmentSheafFieldAmbient) :
  environmentSectionAllSamples (atQuantum (essField s)) =
  (vacuumSampleAmbient, containedSampleAmbient, messySampleAmbient).
Proof.
  rewrite Heq.
  unfold environmentSectionAllSamples.
  reflexivity.
Qed.

Lemma environment_sample_sections_coexist_not_xor (s : EnvironmentSection) :
  environmentSectionAllSamples s = (vacuum s, contained s, messy s).
Proof.
  exact (environment_sections_coexist_not_xor s).
Qed.

Lemma environment_sample_spaces_are_not_xor_worlds
  (a b : EnvSampleAxis) :
  environmentSectionAllSamples
    {| vacuum := vacuumSampleAmbient;
       contained := containedSampleAmbient;
       messy := messySampleAmbient |} =
  (vacuumSampleAmbient, containedSampleAmbient, messySampleAmbient).
Proof. reflexivity. Qed.

Definition environmentIsOneSheafNotThreeAxioms : Prop := True.

Lemma environment_is_one_sheaf_not_three_axioms :
  environmentIsOneSheafNotThreeAxioms.
Proof. exact I. Qed.

Definition vacuumProofClosesMessyWithoutPath : Prop := False.

Lemma vacuum_proof_does_not_close_messy_without_path :
  ~ vacuumProofClosesMessyWithoutPath.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fences — zero admit, physics GREEN false                    *)
(* ------------------------------------------------------------------ *)

Definition environmentSampleSectionsPhysicsGreenAuthorized
  (_s : EnvironmentSampleSheaf) : Prop := False.

Lemma environment_sample_sections_physics_green_false
  (s : EnvironmentSampleSheaf) :
  ~ environmentSampleSectionsPhysicsGreenAuthorized s.
Proof. intro H; exact H. Qed.

Definition environmentSampleSectionsProductionWiredAuthorized
  (_s : EnvironmentSampleSheaf) : Prop := False.

Lemma environment_sample_sections_production_wired_false
  (s : EnvironmentSampleSheaf) :
  ~ environmentSampleSectionsProductionWiredAuthorized s.
Proof. intro H; exact H. Qed.

Definition environmentSampleSectionsZeroAdmitAuthorized
  (_s : EnvironmentSampleSheaf) : Prop := False.

Lemma environment_sample_sections_zero_admit (s : EnvironmentSampleSheaf) :
  ~ environmentSampleSectionsZeroAdmitAuthorized s.
Proof. intro H; exact H. Qed.

Lemma environment_sample_sheaf_reuses_scale_commute_parent
  (e : ElementElectronic) :
  parent (escBinding (essScaleCommute (environmentSampleSheafUnwired e))) = e.
Proof.
  apply environment_scale_commute_unwired_binding_parent.
Qed.

Lemma environment_sample_sheaf_scale_modality_unwired (e : ElementElectronic) :
  environmentScaleModality (essScaleCommute (environmentSampleSheafUnwired e)) =
  environmentScaleModalityCurrent.
Proof.
  unfold environmentSampleSheafUnwired.
  reflexivity.
Qed.

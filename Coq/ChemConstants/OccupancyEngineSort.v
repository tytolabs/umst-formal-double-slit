(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OccupancyEngineSort.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: X29 occupancy-engine **sort conservation**.      *)
(*  Each Z sorts into Madelung family OR one of three finite exception  *)
(*  families (Named La/Ce/Gd/Pt/Au; Actinide Ac–Lr Pu absent; DBlock    *)
(*  Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag). Cites sibling exception modules and      *)
(*  occupancy_exception_sets composition — not a 26th axiom.            *)
(*  Homolog ≠ copy (Ds vs Pt) cited read-only. Modality Unwired.        *)
(*  physics_green = False. Zero Admitted. Not wired lib/eos.           *)
(* ================================================================== *)

Require Import UMST.ChemConstants.NamedOccupancyExceptions.
Require Import UMST.ChemConstants.ActinideOccupancyExceptions.
Require Import UMST.ChemConstants.DBlockOccupancyExceptions.
Require Import UMST.ChemConstants.OccupancyExceptionSetsDisjoint.
From Stdlib Require Import Arith List Bool String Lia.

Open Scope string.

Definition occupancyenginesortSurface : string :=
  "occupancy_engine_sort_surface".

Definition occupancyEngineSortMarker : string :=
  "chem_int_cross_occupancy_engine_sort_v1".

Lemma occupancy_engine_sort_surface_named :
  occupancyenginesortSurface <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_marker_named :
  occupancyEngineSortMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort modality (TYPE-03 preview — Unwired)         *)
(* ------------------------------------------------------------------ *)

Inductive OccupancyEngineSortModality : Type :=
  | occupancy_engine_sort_unwired
  | occupancy_engine_sort_assumed
  | occupancy_engine_sort_proved
  | occupancy_engine_sort_surrogate.

Definition occupancyEngineSortModalityCurrent : OccupancyEngineSortModality :=
  occupancy_engine_sort_unwired.

Definition occupancy_engine_sort_lattice_cardinality : nat := 4.

Lemma occupancy_engine_sort_lattice_cardinality_is_four :
  occupancy_engine_sort_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma occupancy_engine_sort_lattice_not_118_squared :
  negb (Nat.eqb occupancy_engine_sort_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold occupancy_engine_sort_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  X29 cross-classifier row pin                                       *)
(* ------------------------------------------------------------------ *)

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_occupancy_engine_sort_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort bucket — Madelung family vs exception        *)
(* ------------------------------------------------------------------ *)

Inductive OccupancyEngineSortBucket : Type :=
  | sort_bucket_madelung_family
  | sort_bucket_named_exception
  | sort_bucket_actinide_exception
  | sort_bucket_dblock_exception.

Definition occupancyEngineSortBucketTag (b : OccupancyEngineSortBucket) : string :=
  match b with
  | sort_bucket_madelung_family => "madelung_family"
  | sort_bucket_named_exception => "named_exception"
  | sort_bucket_actinide_exception => "actinide_exception"
  | sort_bucket_dblock_exception => "dblock_exception"
  end.

Lemma sort_bucket_madelung_family_tag :
  occupancyEngineSortBucketTag sort_bucket_madelung_family = "madelung_family".
Proof. reflexivity. Qed.

Lemma sort_bucket_named_exception_tag :
  occupancyEngineSortBucketTag sort_bucket_named_exception = "named_exception".
Proof. reflexivity. Qed.

Lemma sort_bucket_actinide_exception_tag :
  occupancyEngineSortBucketTag sort_bucket_actinide_exception = "actinide_exception".
Proof. reflexivity. Qed.

Lemma sort_bucket_dblock_exception_tag :
  occupancyEngineSortBucketTag sort_bucket_dblock_exception = "dblock_exception".
Proof. reflexivity. Qed.

Definition occupancy_engine_sort_bucket_count : nat := 4.

Lemma occupancy_engine_sort_bucket_count_is_four :
  occupancy_engine_sort_bucket_count = 4.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Z-set membership (bool) — cite sibling finite exception lists       *)
(* ------------------------------------------------------------------ *)

Definition natInList (z : nat) (zs : list nat) : bool :=
  existsb (Nat.eqb z) zs.

Definition isNamedExceptionZ (z : nat) : bool :=
  natInList z namedExceptionZList.

Definition isActinideExceptionZ (z : nat) : bool :=
  natInList z actinideExceptionZList.

Definition isDBlockExceptionZ (z : nat) : bool :=
  natInList z dBlockExceptionZList.

Definition isAnyOccupancyExceptionZ (z : nat) : bool :=
  isNamedExceptionZ z || isActinideExceptionZ z || isDBlockExceptionZ z.

Lemma named_exception_in_list (ex : NamedException) :
  In ex namedExceptionList.
Proof.
  destruct ex; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
Qed.

Lemma named_exception_z_in_list (ex : NamedException) :
  In (NamedException_z ex) namedExceptionZList.
Proof.
  apply in_map_iff.
  exists ex.
  split; [reflexivity | apply named_exception_in_list].
Qed.

Lemma named_exception_z_in_list_bool (ex : NamedException) :
  isNamedExceptionZ (NamedException_z ex) = true.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

Lemma actinide_exception_in_list (ex : ActinideException) :
  In ex actinideExceptionList.
Proof.
  destruct ex; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma actinide_exception_z_in_list (ex : ActinideException) :
  In (ActinideException_z ex) actinideExceptionZList.
Proof.
  apply in_map_iff.
  exists ex.
  split; [reflexivity | apply actinide_exception_in_list].
Qed.

Lemma actinide_exception_z_in_list_bool (ex : ActinideException) :
  isActinideExceptionZ (ActinideException_z ex) = true.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

Lemma d_block_exception_in_list (ex : DBlockException) :
  In ex dBlockExceptionList.
Proof.
  destruct ex; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma d_block_exception_z_in_list (ex : DBlockException) :
  In (DBlockException_z ex) dBlockExceptionZList.
Proof.
  apply in_map_iff.
  exists ex.
  split; [reflexivity | apply d_block_exception_in_list].
Qed.

Lemma d_block_exception_z_in_list_bool (ex : DBlockException) :
  isDBlockExceptionZ (DBlockException_z ex) = true.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Occupancy-engine sort classifier (cite occupancy_exception_sets)    *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortBucket (z : nat) : OccupancyEngineSortBucket :=
  if isNamedExceptionZ z then sort_bucket_named_exception
  else if isActinideExceptionZ z then sort_bucket_actinide_exception
  else if isDBlockExceptionZ z then sort_bucket_dblock_exception
  else sort_bucket_madelung_family.

Lemma named_exception_sorts_named_bucket (ex : NamedException) :
  occupancyEngineSortBucket (NamedException_z ex) =
  sort_bucket_named_exception.
Proof.
  unfold occupancyEngineSortBucket.
  rewrite named_exception_z_in_list_bool.
  reflexivity.
Qed.

Lemma actinide_not_named_exception_z (ex : ActinideException) :
  isNamedExceptionZ (ActinideException_z ex) = false.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

Lemma d_block_not_named_exception_z (ex : DBlockException) :
  isNamedExceptionZ (DBlockException_z ex) = false.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

Lemma d_block_not_actinide_exception_z (ex : DBlockException) :
  isActinideExceptionZ (DBlockException_z ex) = false.
Proof.
  destruct ex; simpl; reflexivity.
Qed.

Lemma actinide_exception_sorts_actinide_bucket (ex : ActinideException) :
  occupancyEngineSortBucket (ActinideException_z ex) =
  sort_bucket_actinide_exception.
Proof.
  unfold occupancyEngineSortBucket.
  rewrite actinide_not_named_exception_z.
  rewrite actinide_exception_z_in_list_bool.
  reflexivity.
Qed.

Lemma d_block_exception_sorts_dblock_bucket (ex : DBlockException) :
  occupancyEngineSortBucket (DBlockException_z ex) =
  sort_bucket_dblock_exception.
Proof.
  unfold occupancyEngineSortBucket.
  rewrite d_block_not_named_exception_z.
  rewrite d_block_not_actinide_exception_z.
  rewrite d_block_exception_z_in_list_bool.
  reflexivity.
Qed.

Definition exceptionSetsSortIntoDistinctBuckets : Prop :=
  (forall ex : NamedException,
     occupancyEngineSortBucket (NamedException_z ex) =
     sort_bucket_named_exception) /\
  (forall ex : ActinideException,
     occupancyEngineSortBucket (ActinideException_z ex) =
     sort_bucket_actinide_exception) /\
  (forall ex : DBlockException,
     occupancyEngineSortBucket (DBlockException_z ex) =
     sort_bucket_dblock_exception).

Lemma exception_sets_sort_into_distinct_buckets :
  exceptionSetsSortIntoDistinctBuckets.
Proof.
  repeat split; intros ex;
  [ apply named_exception_sorts_named_bucket
  | apply actinide_exception_sorts_actinide_bucket
  | apply d_block_exception_sorts_dblock_bucket ].
Qed.

(* ------------------------------------------------------------------ *)
(*  Pu (Z=94) Madelung family — absent from all exception Z-lists       *)
(* ------------------------------------------------------------------ *)

Definition plutoniumZ : nat := 94.

Lemma plutonium_z_is_94 : plutoniumZ = 94%nat.
Proof. reflexivity. Qed.

Lemma plutonium_not_any_exception_z :
  isAnyOccupancyExceptionZ plutoniumZ = false.
Proof.
  unfold isAnyOccupancyExceptionZ, plutoniumZ.
  simpl. reflexivity.
Qed.

Lemma plutonium_sorts_madelung_family :
  occupancyEngineSortBucket plutoniumZ = sort_bucket_madelung_family.
Proof.
  unfold occupancyEngineSortBucket, plutoniumZ.
  simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pt / Ds homolog pins — sort bucket vs occupancy copy (read-only)   *)
(* ------------------------------------------------------------------ *)

Definition platinumZ : nat := 78.
Definition darmstadtiumZ : nat := 110.
Definition periodHomologZOffset : nat := 32.

Lemma platinum_z_is_78 : platinumZ = 78%nat.
Proof. reflexivity. Qed.

Lemma darmstadtium_z_is_110 : darmstadtiumZ = 110%nat.
Proof. reflexivity. Qed.

Lemma period_homolog_z_offset_is_32 : periodHomologZOffset = 32%nat.
Proof. reflexivity. Qed.

Lemma ds_pt_homolog_z_offset :
  darmstadtiumZ = platinumZ + periodHomologZOffset.
Proof.
  unfold darmstadtiumZ, platinumZ, periodHomologZOffset.
  reflexivity.
Qed.

Lemma platinum_sorts_named_exception :
  occupancyEngineSortBucket platinumZ = sort_bucket_named_exception.
Proof.
  unfold platinumZ.
  apply (named_exception_sorts_named_bucket named_exception_pt).
Qed.

Lemma darmstadtium_not_named_exception_z :
  isNamedExceptionZ darmstadtiumZ = false.
Proof.
  unfold isNamedExceptionZ, natInList, darmstadtiumZ.
  simpl. reflexivity.
Qed.

Lemma darmstadtium_not_actinide_exception_z :
  isActinideExceptionZ darmstadtiumZ = false.
Proof.
  unfold isActinideExceptionZ, natInList, darmstadtiumZ.
  simpl. reflexivity.
Qed.

Lemma darmstadtium_not_dblock_exception_z :
  isDBlockExceptionZ darmstadtiumZ = false.
Proof.
  unfold isDBlockExceptionZ, natInList, darmstadtiumZ.
  simpl. reflexivity.
Qed.

Lemma darmstadtium_sorts_madelung_family :
  occupancyEngineSortBucket darmstadtiumZ = sort_bucket_madelung_family.
Proof.
  unfold occupancyEngineSortBucket, darmstadtiumZ.
  simpl. reflexivity.
Qed.

Lemma ds_pt_homolog_sort_buckets_distinct :
  occupancyEngineSortBucket platinumZ = sort_bucket_named_exception /\
  occupancyEngineSortBucket darmstadtiumZ = sort_bucket_madelung_family.
Proof.
  split; [apply platinum_sorts_named_exception | apply darmstadtium_sorts_madelung_family].
Qed.

(* Homolog ≠ occupancy copy — read-only cite (INT sibling authority). *)

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma homolog_exception_not_copy_cited :
  homologExceptionNotCopyAuthority <>
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs" ->
  False.
Proof. intro H; apply H; reflexivity. Qed.

Lemma homolog_exception_not_copy_cell_id :
  homologExceptionNotCopyCellId =
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not a 26th axiom — cites madelung_witness / qlattice override pins  *)
(* ------------------------------------------------------------------ *)

Definition soleAxiomCount : nat := 1.

Lemma sole_axiom_count_is_one : soleAxiomCount = 1.
Proof. reflexivity. Qed.

Definition occupancyEngineIsNewAxiom : Prop := False.

Lemma occupancy_engine_not_new_axiom : ~ occupancyEngineIsNewAxiom.
Proof. intro H; exact H. Qed.

Definition observedOverrideNotSecondAxiom : string :=
  "observed_override_config not second axiom".

Lemma observed_override_not_second_axiom :
  observedOverrideNotSecondAxiom <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortCellId : string :=
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-ENGINE-SORT-CONSERVATION".

Definition occupancyEngineSortNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-ENGINE-SORT-CONSERVATION X29 occupancy engine sort conservation Unwired — Madelung family vs Named Actinide DBlock exception families cite occupancy_exception_sets not fork; homolog not copy cite homolog_exception_not_copy; madelung_witness cited; qlattice product factor not XOR; observed_override_config not 26th axiom; Pu94 absent; not physics GREEN; not production_wired".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition occupancyEngineSortQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortMadelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Definition occupancyEngineSortExceptionSetsAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs".

Definition occupancyEngineSortExceptionSetsCellId : string :=
  "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Lemma occupancy_engine_sort_cell_id :
  occupancyEngineSortCellId =
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-ENGINE-SORT-CONSERVATION".
Proof. reflexivity. Qed.

Lemma occupancy_engine_sort_cites_int_authority :
  occupancyEngineSortIntAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma occupancy_engine_sort_cites_qlattice :
  occupancyEngineSortQlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

Lemma occupancy_engine_sort_cites_madelung_witness :
  occupancyEngineSortMadelungWitnessAuthority <>
  "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_cites_exception_sets :
  occupancyEngineSortExceptionSetsAuthority <>
  "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_cites_exception_sets_disjoint :
  occupancyExceptionSetsCellId =
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-EXCEPTION-SETS-DISJOINT".
Proof. apply occupancy_exception_sets_cell_id. Qed.

Lemma occupancy_engine_sort_modality_unwired :
  occupancyEngineSortModalityCurrent = occupancy_engine_sort_unwired.
Proof. reflexivity. Qed.

Lemma occupancy_engine_sort_named_modality_still_unwired :
  namedOccupancyModalityCurrent = named_occupancy_unwired.
Proof. apply named_occupancy_modality_unwired. Qed.

Lemma occupancy_engine_sort_actinide_modality_still_unwired :
  actinideOccupancyModalityCurrent = actinide_occupancy_unwired.
Proof. apply actinide_occupancy_modality_unwired. Qed.

Lemma occupancy_engine_sort_d_block_modality_still_unwired :
  dBlockOccupancyModalityCurrent = d_block_occupancy_unwired.
Proof. apply d_block_occupancy_modality_unwired. Qed.

Lemma occupancy_engine_sort_exception_sets_modality_still_unwired :
  occupancyExceptionSetsModalityCurrent = occupancy_exception_sets_unwired.
Proof. apply occupancy_exception_sets_modality_unwired. Qed.

(* ------------------------------------------------------------------ *)
(*  Row proved fence — Unwired scaffold, not path-census Proved         *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortProved : Prop := False.

Lemma occupancy_engine_sort_not_proved : ~ occupancyEngineSortProved.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortPhysicsGreenAuthorized : Prop := False.

Lemma occupancy_engine_sort_physics_green_false :
  ~ occupancyEngineSortPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma occupancy_engine_sort_named_physics_green_false :
  ~ namedOccupancyPhysicsGreenAuthorized.
Proof. apply named_occupancy_physics_green_false. Qed.

Lemma occupancy_engine_sort_actinide_physics_green_false :
  ~ actinideOccupancyPhysicsGreenAuthorized.
Proof. apply actinide_occupancy_physics_green_false. Qed.

Lemma occupancy_engine_sort_d_block_physics_green_false :
  ~ dBlockOccupancyPhysicsGreenAuthorized.
Proof. apply d_block_occupancy_physics_green_false. Qed.

Lemma occupancy_engine_sort_exception_sets_physics_green_false :
  ~ occupancyExceptionSetsPhysicsGreenAuthorized.
Proof. apply occupancy_exception_sets_physics_green_false. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortProductionWired : Prop := False.

Lemma occupancy_engine_sort_not_production_wired :
  ~ occupancyEngineSortProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

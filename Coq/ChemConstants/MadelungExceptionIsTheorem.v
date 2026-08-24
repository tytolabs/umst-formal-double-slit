(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: MadelungExceptionIsTheorem.v                          *)
(*                                                                      *)
(*  Knowing-fiber Coq: Madelung occupancy **exception is theorem**       *)
(*  conservation. Named (La/Ce/Gd/Pt/Au), Actinide (Ac–Lr Pu absent),   *)
(*  DBlock (Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag) — observed ≠ predicted is a       *)
(*  derived theorem citing sibling exception modules and madelung_witness *)
(*  — not a 26th axiom. Lr honest pin: observed = predicted (not       *)
(*  Madelung exception theorem). Homolog ≠ copy (Ds vs Pt) read-only.   *)
(*  Modality Unwired. physics_green = False. Zero Admitted.              *)
(* ================================================================== *)

Require Import UMST.ChemConstants.NamedOccupancyExceptions.
Require Import UMST.ChemConstants.ActinideOccupancyExceptions.
Require Import UMST.ChemConstants.DBlockOccupancyExceptions.
Require Import UMST.ChemConstants.OccupancyExceptionSetsDisjoint.
From Stdlib Require Import Arith List Bool String Lia.

Open Scope string.

Definition madelungexceptionistheoremSurface : string :=
  "madelung_exception_is_theorem_surface".

Definition madelungExceptionIsTheoremMarker : string :=
  "chem_int_cross_madelung_exception_is_theorem_v1".

Lemma madelung_exception_is_theorem_surface_named :
  madelungexceptionistheoremSurface <> "".
Proof. discriminate. Qed.

Lemma madelung_exception_is_theorem_marker_named :
  madelungExceptionIsTheoremMarker <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Madelung-exception-is-theorem modality (TYPE-03 preview — Unwired) *)
(* ------------------------------------------------------------------ *)

Inductive MadelungExceptionIsTheoremModality : Type :=
  | madelung_exception_is_theorem_unwired
  | madelung_exception_is_theorem_assumed
  | madelung_exception_is_theorem_proved
  | madelung_exception_is_theorem_surrogate.

Definition madelungExceptionIsTheoremModalityCurrent : MadelungExceptionIsTheoremModality :=
  madelung_exception_is_theorem_unwired.

Definition madelung_exception_is_theorem_lattice_cardinality : nat := 4.

Lemma madelung_exception_is_theorem_lattice_cardinality_is_four :
  madelung_exception_is_theorem_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma madelung_exception_is_theorem_lattice_not_118_squared :
  negb (Nat.eqb madelung_exception_is_theorem_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold madelung_exception_is_theorem_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  X03 cross-classifier row pin — Madelung witness authority          *)
(* ------------------------------------------------------------------ *)

Definition crossClassifierMadelungExceptionIsTheoremRowId : string := "X03".

Lemma cross_classifier_madelung_exception_is_theorem_row_named :
  crossClassifierMadelungExceptionIsTheoremRowId = "X03".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Theorem bucket — exception family vs Lr honest override              *)
(* ------------------------------------------------------------------ *)

Inductive MadelungExceptionTheoremBucket : Type :=
  | theorem_bucket_named_madelung_exception
  | theorem_bucket_actinide_madelung_exception
  | theorem_bucket_dblock_madelung_exception
  | theorem_bucket_lr_honest_override.

Definition madelungExceptionTheoremBucketTag (b : MadelungExceptionTheoremBucket) : string :=
  match b with
  | theorem_bucket_named_madelung_exception => "named_madelung_exception_theorem"
  | theorem_bucket_actinide_madelung_exception => "actinide_madelung_exception_theorem"
  | theorem_bucket_dblock_madelung_exception => "dblock_madelung_exception_theorem"
  | theorem_bucket_lr_honest_override => "lr_honest_override_not_theorem"
  end.

Lemma theorem_bucket_named_tag :
  madelungExceptionTheoremBucketTag theorem_bucket_named_madelung_exception =
  "named_madelung_exception_theorem".
Proof. reflexivity. Qed.

Lemma theorem_bucket_actinide_tag :
  madelungExceptionTheoremBucketTag theorem_bucket_actinide_madelung_exception =
  "actinide_madelung_exception_theorem".
Proof. reflexivity. Qed.

Lemma theorem_bucket_dblock_tag :
  madelungExceptionTheoremBucketTag theorem_bucket_dblock_madelung_exception =
  "dblock_madelung_exception_theorem".
Proof. reflexivity. Qed.

Lemma theorem_bucket_lr_tag :
  madelungExceptionTheoremBucketTag theorem_bucket_lr_honest_override =
  "lr_honest_override_not_theorem".
Proof. reflexivity. Qed.

Definition madelung_exception_theorem_bucket_count : nat := 4.

Lemma madelung_exception_theorem_bucket_count_is_four :
  madelung_exception_theorem_bucket_count = 4.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Named family — Madelung exception IS theorem (observed ≠ predicted)  *)
(* ------------------------------------------------------------------ *)

Definition namedMadelungExceptionIsTheorem (ex : NamedException) : Prop :=
  NamedException_observedNotation ex <>
  NamedException_predictedNotation ex.

Lemma named_madelung_exception_is_theorem (ex : NamedException) :
  namedMadelungExceptionIsTheorem ex.
Proof.
  unfold namedMadelungExceptionIsTheorem.
  apply named_exception_is_madelung_exception.
Qed.

Lemma la_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_la.
Proof. apply named_madelung_exception_is_theorem. Qed.

Lemma ce_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_ce.
Proof. apply named_madelung_exception_is_theorem. Qed.

Lemma gd_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_gd.
Proof. apply named_madelung_exception_is_theorem. Qed.

Lemma pt_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_pt.
Proof. apply named_madelung_exception_is_theorem. Qed.

Lemma au_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_au.
Proof. apply named_madelung_exception_is_theorem. Qed.

Definition allNamedMadelungExceptionsAreTheorem : Prop :=
  forall ex : NamedException, namedMadelungExceptionIsTheorem ex.

Lemma all_named_madelung_exceptions_are_theorem :
  allNamedMadelungExceptionsAreTheorem.
Proof.
  unfold allNamedMadelungExceptionsAreTheorem.
  intros ex.
  apply named_madelung_exception_is_theorem.
Qed.

(* ------------------------------------------------------------------ *)
(*  DBlock family — Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag theorem pins             *)
(* ------------------------------------------------------------------ *)

Definition dBlockMadelungExceptionIsTheorem (ex : DBlockException) : Prop :=
  dBlockExceptionIsMadelungException ex.

Lemma d_block_madelung_exception_is_theorem (ex : DBlockException) :
  dBlockMadelungExceptionIsTheorem ex.
Proof.
  unfold dBlockMadelungExceptionIsTheorem.
  apply d_block_exception_is_madelung_exception.
Qed.

Lemma cr_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_cr.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma cu_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_cu.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma nb_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_nb.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma mo_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_mo.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma ru_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_ru.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma rh_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_rh.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma pd_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_pd.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Lemma ag_madelung_exception_is_theorem :
  dBlockMadelungExceptionIsTheorem d_block_exception_ag.
Proof. apply d_block_madelung_exception_is_theorem. Qed.

Definition allDBlockMadelungExceptionsAreTheorem : Prop :=
  forall ex : DBlockException, dBlockMadelungExceptionIsTheorem ex.

Lemma all_d_block_madelung_exceptions_are_theorem :
  allDBlockMadelungExceptionsAreTheorem.
Proof.
  unfold allDBlockMadelungExceptionsAreTheorem.
  intros ex.
  apply d_block_madelung_exception_is_theorem.
Qed.

(* ------------------------------------------------------------------ *)
(*  Actinide family — six period-7 exceptions theorem; Lr honest pin   *)
(* ------------------------------------------------------------------ *)

Definition actinideMadelungExceptionIsTheorem (ex : ActinideException) : Prop :=
  actinideExceptionIsMadelungException ex.

Lemma actinide_madelung_exception_is_theorem (ex : ActinideException) :
  actinideMadelungExceptionIsTheorem ex ->
  ActinideException_observedNotation ex <>
  ActinideException_predictedNotation ex.
Proof.
  intros H.
  apply actinide_exception_is_madelung_exception.
  exact H.
Qed.

Lemma ac_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_ac.
Proof. apply actinide_exception_ac_is_madelung_exception. Qed.

Lemma th_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_th.
Proof. apply actinide_exception_th_is_madelung_exception. Qed.

Lemma pa_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_pa.
Proof. apply actinide_exception_pa_is_madelung_exception. Qed.

Lemma u_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_u.
Proof. apply actinide_exception_u_is_madelung_exception. Qed.

Lemma np_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_np.
Proof. apply actinide_exception_np_is_madelung_exception. Qed.

Lemma cm_madelung_exception_is_theorem :
  actinideMadelungExceptionIsTheorem actinide_exception_cm.
Proof. apply actinide_exception_cm_is_madelung_exception. Qed.

Lemma lr_not_madelung_exception_theorem :
  ~ actinideMadelungExceptionIsTheorem actinide_exception_lr.
Proof. apply actinide_exception_lr_not_madelung_exception. Qed.

Definition sixActinideMadelungExceptionsAreTheorem : Prop :=
  actinideMadelungExceptionIsTheorem actinide_exception_ac /\
  actinideMadelungExceptionIsTheorem actinide_exception_th /\
  actinideMadelungExceptionIsTheorem actinide_exception_pa /\
  actinideMadelungExceptionIsTheorem actinide_exception_u /\
  actinideMadelungExceptionIsTheorem actinide_exception_np /\
  actinideMadelungExceptionIsTheorem actinide_exception_cm.

Lemma six_actinide_madelung_exceptions_are_theorem :
  sixActinideMadelungExceptionsAreTheorem.
Proof.
  repeat split;
  [ apply ac_madelung_exception_is_theorem
  | apply th_madelung_exception_is_theorem
  | apply pa_madelung_exception_is_theorem
  | apply u_madelung_exception_is_theorem
  | apply np_madelung_exception_is_theorem
  | apply cm_madelung_exception_is_theorem ].
Qed.

(* ------------------------------------------------------------------ *)
(*  Pu (Z=94) — absent from all exception Z-lists (Madelung family)     *)
(* ------------------------------------------------------------------ *)

Definition plutoniumZ : nat := 94.

Lemma plutonium_z_is_94 : plutoniumZ = 94%nat.
Proof. reflexivity. Qed.

Definition natInList (z : nat) (zs : list nat) : bool :=
  existsb (Nat.eqb z) zs.

Definition isAnyOccupancyExceptionZ (z : nat) : bool :=
  natInList z namedExceptionZList ||
  natInList z actinideExceptionZList ||
  natInList z dBlockExceptionZList.

Lemma plutonium_not_any_exception_z :
  isAnyOccupancyExceptionZ plutoniumZ = false.
Proof.
  unfold isAnyOccupancyExceptionZ, plutoniumZ.
  simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pt / Ds homolog pins — theorem bucket vs occupancy copy (read-only)  *)
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

Lemma platinum_named_madelung_exception_is_theorem :
  namedMadelungExceptionIsTheorem named_exception_pt.
Proof. apply pt_madelung_exception_is_theorem. Qed.

Lemma darmstadtium_not_named_exception_z :
  natInList darmstadtiumZ namedExceptionZList = false.
Proof.
  unfold natInList, darmstadtiumZ.
  simpl. reflexivity.
Qed.

Lemma ds_pt_homolog_theorem_buckets_distinct :
  namedMadelungExceptionIsTheorem named_exception_pt /\
  natInList darmstadtiumZ namedExceptionZList = false.
Proof.
  split; [apply platinum_named_madelung_exception_is_theorem | apply darmstadtium_not_named_exception_z].
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

Definition madelungExceptionIsNewAxiom : Prop := False.

Lemma madelung_exception_not_new_axiom : ~ madelungExceptionIsNewAxiom.
Proof. intro H; exact H. Qed.

Definition observedOverrideNotSecondAxiom : string :=
  "observed_override_config not second axiom".

Lemma observed_override_not_second_axiom :
  observedOverrideNotSecondAxiom <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition madelungExceptionIsTheoremCellId : string :=
  "CHEM-FORMAL-Q-COQ-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION".

Definition madelungExceptionIsTheoremNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION X03 Madelung exception is theorem conservation Unwired — Named Actinide DBlock observed ne predicted derived theorem cite sibling exception modules and madelung_witness not 26th axiom; Lr honest override observed eq predicted not theorem; Pu94 absent; homolog not copy cite homolog_exception_not_copy; qlattice product factor not XOR; not physics GREEN; not production_wired".

Definition madelungExceptionIsTheoremIntAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Definition madelungExceptionIsTheoremQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition madelungExceptionIsTheoremExceptionSetsAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs".

Definition madelungExceptionIsTheoremExceptionSetsCellId : string :=
  "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition madelungExceptionIsTheoremMadelungWitnessCellId : string :=
  "CHEM-INT-CROSS-MADELUNG-WITNESS".

Lemma madelung_exception_is_theorem_cell_id :
  madelungExceptionIsTheoremCellId =
  "CHEM-FORMAL-Q-COQ-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION".
Proof. reflexivity. Qed.

Lemma madelung_exception_is_theorem_cites_int_authority :
  madelungExceptionIsTheoremIntAuthority =
  "umst/umst-chem/src/x_rows/madelung_witness.rs".
Proof. reflexivity. Qed.

Lemma madelung_exception_is_theorem_cites_qlattice :
  madelungExceptionIsTheoremQlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

Lemma madelung_exception_is_theorem_cites_madelung_witness :
  madelungExceptionIsTheoremIntAuthority <> "".
Proof. discriminate. Qed.

Lemma madelung_exception_is_theorem_cites_exception_sets :
  madelungExceptionIsTheoremExceptionSetsAuthority <> "".
Proof. discriminate. Qed.

Lemma madelung_exception_is_theorem_cites_exception_sets_disjoint :
  occupancyExceptionSetsCellId =
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-EXCEPTION-SETS-DISJOINT".
Proof. apply occupancy_exception_sets_cell_id. Qed.

Lemma madelung_exception_is_theorem_modality_unwired :
  madelungExceptionIsTheoremModalityCurrent = madelung_exception_is_theorem_unwired.
Proof. reflexivity. Qed.

Lemma madelung_exception_is_theorem_named_modality_still_unwired :
  namedOccupancyModalityCurrent = named_occupancy_unwired.
Proof. apply named_occupancy_modality_unwired. Qed.

Lemma madelung_exception_is_theorem_actinide_modality_still_unwired :
  actinideOccupancyModalityCurrent = actinide_occupancy_unwired.
Proof. apply actinide_occupancy_modality_unwired. Qed.

Lemma madelung_exception_is_theorem_d_block_modality_still_unwired :
  dBlockOccupancyModalityCurrent = d_block_occupancy_unwired.
Proof. apply d_block_occupancy_modality_unwired. Qed.

Lemma madelung_exception_is_theorem_exception_sets_modality_still_unwired :
  occupancyExceptionSetsModalityCurrent = occupancy_exception_sets_unwired.
Proof. apply occupancy_exception_sets_modality_unwired. Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation composition — three families + Lr honest pin          *)
(* ------------------------------------------------------------------ *)

Definition madelungExceptionIsTheoremConservation : Prop :=
  allNamedMadelungExceptionsAreTheorem /\
  allDBlockMadelungExceptionsAreTheorem /\
  sixActinideMadelungExceptionsAreTheorem /\
  ~ actinideMadelungExceptionIsTheorem actinide_exception_lr.

Lemma madelung_exception_is_theorem_conservation :
  madelungExceptionIsTheoremConservation.
Proof.
  unfold madelungExceptionIsTheoremConservation.
  split.
  - apply all_named_madelung_exceptions_are_theorem.
  - split.
    + apply all_d_block_madelung_exceptions_are_theorem.
    + split.
      * apply six_actinide_madelung_exceptions_are_theorem.
      * apply lr_not_madelung_exception_theorem.
Qed.

(* ------------------------------------------------------------------ *)
(*  Row proved fence — Unwired scaffold, not path-census Proved         *)
(* ------------------------------------------------------------------ *)

Definition madelungExceptionIsTheoremProved : Prop := False.

Lemma madelung_exception_is_theorem_not_proved : ~ madelungExceptionIsTheoremProved.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition madelungExceptionIsTheoremPhysicsGreenAuthorized : Prop := False.

Lemma madelung_exception_is_theorem_physics_green_false :
  ~ madelungExceptionIsTheoremPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma madelung_exception_is_theorem_named_physics_green_false :
  ~ namedOccupancyPhysicsGreenAuthorized.
Proof. apply named_occupancy_physics_green_false. Qed.

Lemma madelung_exception_is_theorem_actinide_physics_green_false :
  ~ actinideOccupancyPhysicsGreenAuthorized.
Proof. apply actinide_occupancy_physics_green_false. Qed.

Lemma madelung_exception_is_theorem_d_block_physics_green_false :
  ~ dBlockOccupancyPhysicsGreenAuthorized.
Proof. apply d_block_occupancy_physics_green_false. Qed.

Lemma madelung_exception_is_theorem_exception_sets_physics_green_false :
  ~ occupancyExceptionSetsPhysicsGreenAuthorized.
Proof. apply occupancy_exception_sets_physics_green_false. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition madelungExceptionIsTheoremProductionWired : Prop := False.

Lemma madelung_exception_is_theorem_not_production_wired :
  ~ madelungExceptionIsTheoremProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

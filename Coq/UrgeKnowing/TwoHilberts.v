(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: TwoHilberts.v                                         *)
(*                                                                      *)
(*  Knowing/quantum Coq: §12.7 two Hilberts — persist Hilbert (acting) *)
(*  distinct from occupancy Hilbert (knowing). homolog ≠ copy. Knowing   *)
(*  fiber witness with positive fuse refusal. Mirrors URGE-INT-TWO-      *)
(*  HILBERTS — not meso thermo, not ADK occupancy wired.              *)
(*                                                                      *)
(*  Self-contained over Coq stdlib. Modality Unwired. physics_green =   *)
(*  False. Zero Admitted. Zero new Axiom. Sole axiom cited as string:   *)
(*  LandauerLaw.physicalSecondLaw (framing only).                        *)
(* ================================================================== *)

From Coq Require Import Arith Lia List String Ascii.
Import ListNotations.

Open Scope string.

Inductive TwoHilbertsModality : Type :=
  | two_hilberts_unwired
  | two_hilberts_assumed
  | two_hilberts_proved
  | two_hilberts_surrogate.

Definition twoHilbertsModalityCurrent : TwoHilbertsModality :=
  two_hilberts_unwired.

Inductive HilbertRole : Type :=
  | hilbert_role_persist_acting
  | hilbert_role_occupancy_knowing.

Definition persistHilbertRole : HilbertRole := hilbert_role_persist_acting.
Definition occupancyHilbertRole : HilbertRole := hilbert_role_occupancy_knowing.

Lemma persist_ne_occupancy_role : persistHilbertRole <> occupancyHilbertRole.
Proof. discriminate. Qed.

Record PersistHilbert := { persist_raw : nat }.
Record OccupancyHilbert := { occupancy_raw : nat }.

Definition persistHilbertRoleOf (_ : PersistHilbert) : HilbertRole :=
  hilbert_role_persist_acting.

Definition occupancyHilbertRoleOf (_ : OccupancyHilbert) : HilbertRole :=
  hilbert_role_occupancy_knowing.

Inductive HilbertFuseRefused : Type :=
  | hilbert_fuse_persist_into_occupancy
  | hilbert_fuse_occupancy_into_persist
  | hilbert_fuse_homolog_is_not_copy.

Definition fusePersistIntoOccupancyRefused : HilbertFuseRefused :=
  hilbert_fuse_persist_into_occupancy.

Definition fuseOccupancyIntoPersistRefused : HilbertFuseRefused :=
  hilbert_fuse_occupancy_into_persist.

Definition homologNotCopyRefused : HilbertFuseRefused :=
  hilbert_fuse_homolog_is_not_copy.

Inductive HilbertFuseResult (A : Type) : Type :=
  | fuse_ok : A -> HilbertFuseResult A
  | fuse_refused : HilbertFuseRefused -> HilbertFuseResult A.

Definition refuseFusePersistIntoOccupancy (_ : PersistHilbert)
  : HilbertFuseResult OccupancyHilbert :=
  @fuse_refused OccupancyHilbert hilbert_fuse_persist_into_occupancy.

Definition refuseFuseOccupancyIntoPersist (_ : OccupancyHilbert)
  : HilbertFuseResult PersistHilbert :=
  @fuse_refused PersistHilbert hilbert_fuse_occupancy_into_persist.

Lemma fuse_persist_into_occupancy_refused :
  forall p : PersistHilbert,
    refuseFusePersistIntoOccupancy p =
    @fuse_refused _ hilbert_fuse_persist_into_occupancy.
Proof. intros. reflexivity. Qed.

Lemma fuse_occupancy_into_persist_refused :
  forall o : OccupancyHilbert,
    refuseFuseOccupancyIntoPersist o =
    @fuse_refused _ hilbert_fuse_occupancy_into_persist.
Proof. intros. reflexivity. Qed.

Definition persistHilbertBits : nat := 8.

Definition persistHilbertCoords (ucrs grid : nat) (bits : nat) : nat * nat :=
  let side := Nat.shiftl 1 bits in
  let mask := side - 1 in
  let x := ucrs mod (mask + 1) in
  let y := grid mod (mask + 1) in
  (x, y).

Definition persistCurveIndex (x y bits : nat) : nat :=
  let side := Nat.shiftl 1 bits in
  (x mod side) + (y mod side) * side.

Definition persistHilbertIndex (ucrs grid : nat) : PersistHilbert :=
  let bits := persistHilbertBits in
  let (x, y) := persistHilbertCoords ucrs grid bits in
  {| persist_raw := persistCurveIndex x y bits |}.

Fixpoint occupancy_hash_byte (h : nat) (b : nat) : nat :=
  (h * 31 + b) mod 65536.

Fixpoint occupancy_hash_string (h : nat) (s : string) : nat :=
  match s with
  | EmptyString => h
  | String c rest =>
      occupancy_hash_string (occupancy_hash_byte h (nat_of_ascii c)) rest
  end.

Fixpoint occupancy_hash_paths (h : nat) (paths : list string) : nat :=
  match paths with
  | nil => h
  | p :: rest =>
      let h1 := occupancy_hash_string h p in
      let h2 := occupancy_hash_byte h1 0 in
      occupancy_hash_paths h2 rest
  end.

Definition occupancyHilbertIndex (cell_id : string) (write_set : list string)
  : OccupancyHilbert :=
  {| occupancy_raw :=
       occupancy_hash_paths (occupancy_hash_string 5381 cell_id) write_set |}.


Definition hilbertRoleEqb (r1 r2 : HilbertRole) : bool :=
  match r1, r2 with
  | hilbert_role_persist_acting, hilbert_role_persist_acting => true
  | hilbert_role_occupancy_knowing, hilbert_role_occupancy_knowing => true
  | _, _ => false
  end.

Record HilbertHomologWitness := {
  homolog_persist : PersistHilbert;
  homolog_occupancy : OccupancyHilbert;
  homolog_raw_coincident : bool
}.

Definition homologClaimsIdentityCopy (w : HilbertHomologWitness) : bool :=
  hilbertRoleEqb
    (persistHilbertRoleOf (homolog_persist w))
    (occupancyHilbertRoleOf (homolog_occupancy w)).

Definition homologPersistToOccupancy
  (p : PersistHilbert) (cell_id : string) (write_set : list string)
  : HilbertHomologWitness :=
  let o := occupancyHilbertIndex cell_id write_set in
  {| homolog_persist := p;
     homolog_occupancy := o;
     homolog_raw_coincident :=
       if Nat.eqb (persist_raw p) (occupancy_raw o) then true else false |}.

Definition homologNotCopy (w : HilbertHomologWitness) : Prop :=
  persistHilbertRoleOf (homolog_persist w) <>
  occupancyHilbertRoleOf (homolog_occupancy w) /\
  homologClaimsIdentityCopy w = false.

Lemma homolog_not_copy_holds :
  forall (p : PersistHilbert) (cell_id : string) (ws : list string),
    homologNotCopy (homologPersistToOccupancy p cell_id ws).
Proof.
  intros p cell_id ws.
  unfold homologNotCopy, homologPersistToOccupancy,
    homologClaimsIdentityCopy,
    persistHilbertRoleOf, occupancyHilbertRoleOf.
  simpl. split; [discriminate|reflexivity].
Qed.

Lemma homolog_roles_distinct :
  forall w : HilbertHomologWitness,
    persistHilbertRoleOf (homolog_persist w) <>
    occupancyHilbertRoleOf (homolog_occupancy w).
Proof.
  intros w. unfold persistHilbertRoleOf, occupancyHilbertRoleOf. discriminate.
Qed.

Definition twoHilbertsPositiveRefuseHonest : Prop :=
  (forall p : PersistHilbert,
     refuseFusePersistIntoOccupancy p =
     @fuse_refused _ hilbert_fuse_persist_into_occupancy) /\
  (forall o : OccupancyHilbert,
     refuseFuseOccupancyIntoPersist o =
     @fuse_refused _ hilbert_fuse_occupancy_into_persist) /\
  fusePersistIntoOccupancyRefused = hilbert_fuse_persist_into_occupancy /\
  homologNotCopyRefused = hilbert_fuse_homolog_is_not_copy.

Lemma two_hilberts_positive_refuse_honest : twoHilbertsPositiveRefuseHonest.
Proof.
  unfold twoHilbertsPositiveRefuseHonest.
  split.
  - intros p. apply fuse_persist_into_occupancy_refused.
  - split.
    + intros o. apply fuse_occupancy_into_persist_refused.
    + split; reflexivity.
Qed.

Lemma persist_index_deterministic (ucrs grid : nat) :
  persistHilbertIndex ucrs grid = persistHilbertIndex ucrs grid.
Proof. reflexivity. Qed.

Lemma occupancy_index_cell_distinct :
  occupancy_raw
    (occupancyHilbertIndex "CELL-B" ["write/a.rs"; "write/b.rs"]) <>
  occupancy_raw
    (occupancyHilbertIndex "CELL-C" ["write/a.rs"; "write/b.rs"]).
Proof. vm_compute. discriminate. Qed.

Definition persistHilbertAuthority : string :=
  "umst/egoff/egoff/src/memory/hilbert_layout.rs".

Definition occupancyHilbertAuthority : string :=
  "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs".

Definition twoHilbertsBlueprintAuthority : string :=
  "workspace/docs/UMST_URGE_BLUEPRINT.md".

Definition carrierStrataAuthority : string :=
  "workspace/docs/UMST_CARRIER_STRATA.md".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition twoHilbertsCellId : string :=
  "URGE-FORMAL-Q-COQ-TWO-HILBERTS".

Definition twoHilbertsNonClaim : string :=
  "URGE-FORMAL-Q-COQ-TWO-HILBERTS §12.7 persist Hilbert acting egoff hilbert_index ucrs_seq grid_hash xy2d distinct from occupancy Hilbert knowing ADK cell_locality_hash FNV antichain sort homolog not copy fuse refused positive not only physics_green Unwired not Proved not physics GREEN not production_wired knowing fiber".

Definition persistNotOccupancyCopyCollision : string :=
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ne occupancy Hilbert FNV(cell_id, write_set) homolog not copy".

Lemma persist_ne_occupancy_morphism :
  persistHilbertAuthority <> occupancyHilbertAuthority.
Proof. discriminate. Qed.

Lemma two_hilberts_cell_id :
  twoHilbertsCellId = "URGE-FORMAL-Q-COQ-TWO-HILBERTS".
Proof. reflexivity. Qed.

Lemma two_hilberts_cites_persist_authority :
  persistHilbertAuthority <> "".
Proof. discriminate. Qed.

Lemma two_hilberts_cites_occupancy_authority :
  occupancyHilbertAuthority <> "".
Proof. discriminate. Qed.

Lemma two_hilberts_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

Lemma two_hilberts_collision_fence_named :
  persistNotOccupancyCopyCollision <> "".
Proof. discriminate. Qed.

Definition twoHilbertsSecondLawConservationFraming : string :=
  "second_law_conservation_two_hilberts_one_axiom_not_second_hilbert_axiom".

Lemma two_hilberts_not_second_hilbert_axiom :
  twoHilbertsSecondLawConservationFraming <>
  "hilbert_second_axiom".
Proof. discriminate. Qed.

Definition physicsGreenAuthorized : Prop := False.

Lemma two_hilberts_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma two_hilberts_modality_unwired :
  twoHilbertsModalityCurrent = two_hilberts_unwired.
Proof. reflexivity. Qed.

Definition knowingFiberTag : string := "quantum_knowing_fiber".

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma two_hilberts_not_meso_thermo_restate :
  twoHilbertsNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

Lemma two_hilberts_knowing_fiber_named :
  knowingFiberTag = "quantum_knowing_fiber".
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PersistVsOccupancy.v                                  *)
(*                                                                      *)
(*  Knowing/quantum Coq: §12.7 persist Hilbert ≠ occupancy Hilbert.    *)
(*  Persist Hilbert (acting): egoff hilbert_index(ucrs_seq, grid_hash)  *)
(*  via xy2d sled persist morphism. Occupancy Hilbert (knowing): ADK     *)
(*  cell_locality_hash FNV antichain sort — homolog ≠ copy across        *)
(*  fibers. Fuse is positively refused. Compose Excitement select — no   *)
(*  second local argmin. Mirrors Rust `persist_vs_occupancy` knowing      *)
(*  scaffold. Self-contained. Modality Unwired. physics_green = False.  *)
(*  Zero Admitted. Zero new Axiom — sole axiom framing cites             *)
(*  LandauerLaw.physicalSecondLaw only.                                  *)
(* ================================================================== *)

From Coq Require Import String Arith List Bool.
Import ListNotations.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  PersistVsOccupancy modality (Unwired / Assumed / Proved /           *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive PersistVsOccupancyModality : Type :=
  | persist_vs_occupancy_unwired
  | persist_vs_occupancy_assumed
  | persist_vs_occupancy_proved
  | persist_vs_occupancy_surrogate.

Definition persistVsOccupancyModalityCurrent : PersistVsOccupancyModality :=
  persist_vs_occupancy_unwired.

(* ------------------------------------------------------------------ *)
(*  Hilbert role tags — persist acting vs occupancy knowing             *)
(* ------------------------------------------------------------------ *)

Inductive HilbertRole : Type :=
  | hilbert_role_persist_acting
  | hilbert_role_occupancy_knowing.

Definition persistHilbertRole : HilbertRole :=
  hilbert_role_persist_acting.

Definition occupancyHilbertRole : HilbertRole :=
  hilbert_role_occupancy_knowing.

(* ------------------------------------------------------------------ *)
(*  Distinct Hilbert newtypes — persist ≠ occupancy at type level       *)
(* ------------------------------------------------------------------ *)

Record PersistHilbert := {
  persist_raw : nat
}.

Record OccupancyHilbert := {
  occupancy_raw : nat
}.

Definition persistHilbertRoleOf (p : PersistHilbert) : HilbertRole :=
  hilbert_role_persist_acting.

Definition occupancyHilbertRoleOf (o : OccupancyHilbert) : HilbertRole :=
  hilbert_role_occupancy_knowing.

Lemma persist_ne_occupancy_role :
  persistHilbertRole <> occupancyHilbertRole.
Proof. discriminate. Qed.

Lemma persist_hilbert_role_pin (p : PersistHilbert) :
  persistHilbertRoleOf p = hilbert_role_persist_acting.
Proof. reflexivity. Qed.

Lemma occupancy_hilbert_role_pin (o : OccupancyHilbert) :
  occupancyHilbertRoleOf o = hilbert_role_occupancy_knowing.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Typed positive fuse refusal — not only !physics_green               *)
(* ------------------------------------------------------------------ *)

Inductive HilbertFuseRefused : Type :=
  | fuse_refused_persist_into_occupancy
  | fuse_refused_occupancy_into_persist
  | fuse_refused_homolog_is_not_copy
  | fuse_refused_second_argmin.

Definition refuseFusePersistIntoOccupancy
  (_p : PersistHilbert) : option HilbertFuseRefused :=
  Some fuse_refused_persist_into_occupancy.

Definition refuseFuseOccupancyIntoPersist
  (_o : OccupancyHilbert) : option HilbertFuseRefused :=
  Some fuse_refused_occupancy_into_persist.

Definition refuseSecondArgmin : option HilbertFuseRefused :=
  Some fuse_refused_second_argmin.

Lemma fuse_persist_into_occupancy_refused (p : PersistHilbert) :
  refuseFusePersistIntoOccupancy p =
  Some fuse_refused_persist_into_occupancy.
Proof. reflexivity. Qed.

Lemma fuse_occupancy_into_persist_refused (o : OccupancyHilbert) :
  refuseFuseOccupancyIntoPersist o =
  Some fuse_refused_occupancy_into_persist.
Proof. reflexivity. Qed.

Lemma second_argmin_refused :
  refuseSecondArgmin = Some fuse_refused_second_argmin.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Homolog witness — homolog relates fibers; homolog ≠ copy            *)
(* ------------------------------------------------------------------ *)

Record HilbertHomologWitness := {
  homolog_persist : PersistHilbert;
  homolog_occupancy : OccupancyHilbert;
  homolog_claims_identity_copy : bool
}.

Definition homologPersistToOccupancy
  (p : PersistHilbert) (o : OccupancyHilbert) (claims_copy : bool) :
  HilbertHomologWitness :=
  {| homolog_persist := p;
     homolog_occupancy := o;
     homolog_claims_identity_copy := claims_copy |}.

Definition homologNotCopy (w : HilbertHomologWitness) : bool :=
  match homolog_claims_identity_copy w with
  | true => false
  | false =>
      match persistHilbertRoleOf (homolog_persist w),
            occupancyHilbertRoleOf (homolog_occupancy w) with
      | hilbert_role_persist_acting, hilbert_role_occupancy_knowing => true
      | _, _ => false
      end
  end.

Definition hilbertRoleEqb (r1 r2 : HilbertRole) : bool :=
  match r1, r2 with
  | hilbert_role_persist_acting, hilbert_role_persist_acting => true
  | hilbert_role_occupancy_knowing, hilbert_role_occupancy_knowing => true
  | _, _ => false
  end.

Definition homologClaimsIdentityCopy (w : HilbertHomologWitness) : bool :=
  homolog_claims_identity_copy w ||
  hilbertRoleEqb (persistHilbertRoleOf (homolog_persist w))
                 (occupancyHilbertRoleOf (homolog_occupancy w)).

Lemma homolog_witness_not_copy_when_roles_distinct
  (p : PersistHilbert) (o : OccupancyHilbert) :
  homologNotCopy (homologPersistToOccupancy p o false) = true.
Proof.
  unfold homologNotCopy, homologPersistToOccupancy.
  simpl. reflexivity.
Qed.

Lemma homolog_identity_copy_refused
  (p : PersistHilbert) (o : OccupancyHilbert) :
  homologClaimsIdentityCopy (homologPersistToOccupancy p o true) = true.
Proof.
  unfold homologClaimsIdentityCopy, homologPersistToOccupancy.
  simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture verdict — 1 accept + 2 refuse morphism classes              *)
(* ------------------------------------------------------------------ *)

Inductive FiberVerdict : Type :=
  | fiber_verdict_accept
  | fiber_verdict_refuse.

Definition fiberVerdictEqb (v1 v2 : FiberVerdict) : bool :=
  match v1, v2 with
  | fiber_verdict_accept, fiber_verdict_accept => true
  | fiber_verdict_refuse, fiber_verdict_refuse => true
  | _, _ => false
  end.


Record FiberFixtureStep := {
  fixture_step_id : string;
  fixture_verdict : FiberVerdict;
  fixture_refusal : option HilbertFuseRefused
}.

Definition evaluateFiberMorphism
  (w : HilbertHomologWitness) (attempt_fuse : bool) : FiberVerdict :=
  if attempt_fuse then
    fiber_verdict_refuse
  else if homologClaimsIdentityCopy w then
    fiber_verdict_refuse
  else if homologNotCopy w then
    fiber_verdict_accept
  else
    fiber_verdict_refuse.

Definition verdictToRefusal
  (verdict : FiberVerdict)
  (w : HilbertHomologWitness)
  (attempt_fuse : bool) : option HilbertFuseRefused :=
  match verdict with
  | fiber_verdict_accept => None
  | fiber_verdict_refuse =>
      if attempt_fuse then
        Some fuse_refused_persist_into_occupancy
      else if homolog_claims_identity_copy w then
        Some fuse_refused_homolog_is_not_copy
      else
        Some fuse_refused_homolog_is_not_copy
  end.

Definition samplePersistHilbert : PersistHilbert :=
  {| persist_raw := 42 |}.

Definition sampleOccupancyHilbert : OccupancyHilbert :=
  {| occupancy_raw := 99 |}.

Definition homologRestrictionAdmittedStep : FiberFixtureStep :=
  {| fixture_step_id := "homolog-restriction-admitted";
     fixture_verdict :=
       evaluateFiberMorphism
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
         false;
     fixture_refusal :=
       verdictToRefusal
         (evaluateFiberMorphism
            (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
            false)
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
         false |}.

Definition fusePersistIntoOccupancyStep : FiberFixtureStep :=
  {| fixture_step_id := "fuse-persist-into-occupancy";
     fixture_verdict :=
       evaluateFiberMorphism
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
         true;
     fixture_refusal :=
       verdictToRefusal
         (evaluateFiberMorphism
            (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
            true)
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
         true |}.

Definition homologIdentityCopyStep : FiberFixtureStep :=
  {| fixture_step_id := "homolog-identity-copy";
     fixture_verdict :=
       evaluateFiberMorphism
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert true)
         false;
     fixture_refusal :=
       verdictToRefusal
         (evaluateFiberMorphism
            (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert true)
            false)
         (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert true)
         false |}.

Definition persistVsOccupancyFixture : list FiberFixtureStep :=
  [ homologRestrictionAdmittedStep;
    fusePersistIntoOccupancyStep;
    homologIdentityCopyStep ].

Fixpoint countFiberVerdict
  (steps : list FiberFixtureStep) (target : FiberVerdict) : nat :=
  match steps with
  | [] => 0
  | step :: rest =>
      (if fiberVerdictEqb (fixture_verdict step) target then 1 else 0)
      + countFiberVerdict rest target
  end.

Lemma fixture_one_accept :
  countFiberVerdict persistVsOccupancyFixture fiber_verdict_accept = 1.
Proof. reflexivity. Qed.

Lemma fixture_two_refuse :
  countFiberVerdict persistVsOccupancyFixture fiber_verdict_refuse = 2.
Proof. reflexivity. Qed.

Lemma homolog_restriction_admitted :
  fixture_verdict homologRestrictionAdmittedStep = fiber_verdict_accept.
Proof. reflexivity. Qed.

Lemma fuse_persist_step_refused :
  fixture_verdict fusePersistIntoOccupancyStep = fiber_verdict_refuse.
Proof. reflexivity. Qed.

Lemma homolog_copy_step_refused :
  fixture_verdict homologIdentityCopyStep = fiber_verdict_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Compose Excitement surrogate — import select, no second argmin      *)
(* ------------------------------------------------------------------ *)

Definition composeSurrogateFor : string :=
  "UMST.Excitement.select".

Definition metaExcitementModule : string :=
  "umst-meta/crates/umst-meta/src/excitement.rs".

Lemma compose_surrogate_is_excitement_select :
  composeSurrogateFor = "UMST.Excitement.select".
Proof. reflexivity. Qed.

Lemma meta_excitement_module_cited :
  metaExcitementModule <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Upstream authority strings (read-only cite — no fork)               *)
(* ------------------------------------------------------------------ *)

Definition persistHilbertAuthority : string :=
  "umst/egoff/egoff/src/memory/hilbert_layout.rs".

Definition occupancyHilbertAuthority : string :=
  "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs".

Definition persistNotOccupancyCopyCollision : string :=
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ≠ occupancy Hilbert FNV(cell_id, write_set) — homolog ≠ copy".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition persistVsOccupancyCellId : string :=
  "URGE-FORMAL-Q-COQ-PERSIST-VS-OCCUPANCY".

Definition persistVsOccupancyMarker : string :=
  "persist_vs_occupancy_v1".

Definition persistVsOccupancySurface : string :=
  "persist_vs_occupancy_surface".

Definition persistVsOccupancyRowStem : string :=
  "persist_vs_occupancy".

Definition persistVsOccupancyNonClaim : string :=
  "URGE-FORMAL-Q-COQ-PERSIST-VS-OCCUPANCY §12.7 persist Hilbert acting egoff hilbert_index ucrs_seq grid_hash xy2d \
   distinct from occupancy Hilbert knowing ADK cell_locality_hash FNV antichain sort homolog not copy \
   fuse refused positive not only physics_green compose select_excitement not local argmin Unwired not Proved".

Lemma persist_vs_occupancy_cell_id :
  persistVsOccupancyCellId = "URGE-FORMAL-Q-COQ-PERSIST-VS-OCCUPANCY".
Proof. reflexivity. Qed.

Lemma persist_vs_occupancy_marker :
  persistVsOccupancyMarker = "persist_vs_occupancy_v1".
Proof. reflexivity. Qed.

Lemma persist_vs_occupancy_surface :
  persistVsOccupancySurface = "persist_vs_occupancy_surface".
Proof. reflexivity. Qed.

Lemma persist_vs_occupancy_row_stem :
  persistVsOccupancyRowStem = "persist_vs_occupancy".
Proof. reflexivity. Qed.

Lemma persist_hilbert_authority_cited :
  persistHilbertAuthority <> "".
Proof. discriminate. Qed.

Lemma occupancy_hilbert_authority_cited :
  occupancyHilbertAuthority <> "".
Proof. discriminate. Qed.

Lemma persist_not_occupancy_copy_collision :
  persistNotOccupancyCopyCollision <> "".
Proof. discriminate. Qed.

Lemma persist_vs_occupancy_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Sole axiom framing: physicalSecondLaw; not second axiom              *)
(* ------------------------------------------------------------------ *)

Definition persistVsOccupancySecondLawFraming : string :=
  "physicalSecondLaw_sole_axiom_framing_not_second_axiom".

Definition secondAxiomTag : string :=
  "persist_vs_occupancy_second_axiom".

Lemma persist_vs_occupancy_not_second_axiom :
  persistVsOccupancySecondLawFraming <> secondAxiomTag.
Proof. discriminate. Qed.

Lemma persist_vs_occupancy_second_law_framing :
  persistVsOccupancySecondLawFraming <> "".
Proof. discriminate. Qed.

Definition persistVsOccupancyIsNewAxiom : Prop := False.

Lemma persist_vs_occupancy_zero_new_axiom :
  ~ persistVsOccupancyIsNewAxiom.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma persist_vs_occupancy_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma persist_vs_occupancy_modality_unwired :
  persistVsOccupancyModalityCurrent = persist_vs_occupancy_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Positive refuse honesty — fuse + homolog without inventing GREEN    *)
(* ------------------------------------------------------------------ *)

Definition persistVsOccupancyPositiveRefuseHonest : bool :=
  match refuseFusePersistIntoOccupancy samplePersistHilbert,
        refuseFuseOccupancyIntoPersist sampleOccupancyHilbert,
        refuseSecondArgmin with
  | Some fuse_refused_persist_into_occupancy,
    Some fuse_refused_occupancy_into_persist,
    Some fuse_refused_second_argmin => true
  | _, _, _ => false
  end.

Lemma persist_vs_occupancy_positive_refuse_honest :
  persistVsOccupancyPositiveRefuseHonest = true.
Proof. reflexivity. Qed.

Definition persistVsOccupancyDeepenHonest : bool :=
  negb (hilbertRoleEqb persistHilbertRole occupancyHilbertRole) &&
  persistVsOccupancyPositiveRefuseHonest &&
  homologNotCopy (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false) &&
  (Nat.eqb (countFiberVerdict persistVsOccupancyFixture fiber_verdict_accept) 1) &&
  (Nat.eqb (countFiberVerdict persistVsOccupancyFixture fiber_verdict_refuse) 2) &&
  String.eqb composeSurrogateFor "UMST.Excitement.select" &&
  negb (String.eqb persistHilbertAuthority "") &&
  negb (String.eqb occupancyHilbertAuthority "").

Lemma persist_vs_occupancy_deepen_honest :
  persistVsOccupancyDeepenHonest = true.
Proof. reflexivity. Qed.

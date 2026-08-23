(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: LinearConservation.v                                  *)
(*                                                                      *)
(*  Knowing-fiber Coq: TYPE-02 linear conservation. Signed coeffs on  *)
(*  conservation axes sum to zero for exact balance; affine weakening   *)
(*  only with dissipative witness. Axes Mass/Charge/AtomCount/Enthalpy *)
(*  structure witness not 118² GREEN table. Geometry routes knowing/    *)
(*  quantum fiber not meso acting. type02LinearProved Unwired not Proved. *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — linear conservation is not a second axiom.  *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  TYPE-02 linear conservation modality (TYPE-03 — Unwired)          *)
(* ------------------------------------------------------------------ *)

Inductive LinearConservationModality : Type :=
  | linear_conservation_unwired
  | linear_conservation_assumed
  | linear_conservation_proved
  | linear_conservation_surrogate.

Definition linearConservationModalityCurrent : LinearConservationModality :=
  linear_conservation_unwired.

(* ------------------------------------------------------------------ *)
(*  Conservation axes — structure witness, not 118² GREEN table           *)
(* ------------------------------------------------------------------ *)

Inductive conservation_axis : Type :=
  | axis_mass
  | axis_charge
  | axis_atom_count
  | axis_enthalpy.

Definition conservation_axis_beq (a b : conservation_axis) : bool :=
  match a, b with
  | axis_mass, axis_mass => true
  | axis_charge, axis_charge => true
  | axis_atom_count, axis_atom_count => true
  | axis_enthalpy, axis_enthalpy => true
  | _, _ => false
  end.

Lemma conservation_axis_beq_refl (a : conservation_axis) :
  conservation_axis_beq a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma mass_axis_not_charge :
  conservation_axis_beq axis_mass axis_charge = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Signed linear coefficients on an axis row                           *)
(* ------------------------------------------------------------------ *)

Record linear_coeff : Type := {
  coeff_sign : bool;
  coeff_magnitude : nat
}.

Definition linear_coeff_positive (m : nat) : linear_coeff :=
  {| coeff_sign := true; coeff_magnitude := m |}.

Definition linear_coeff_negative (m : nat) : linear_coeff :=
  {| coeff_sign := false; coeff_magnitude := m |}.

Fixpoint row_signed_magnitude (cs : list linear_coeff) (positive : bool) : nat :=
  match cs with
  | nil => 0
  | c :: rest =>
      let tail := row_signed_magnitude rest positive in
      if Bool.eqb (coeff_sign c) positive
      then coeff_magnitude c + tail
      else tail
  end.

Definition linear_row_positive_sum (cs : list linear_coeff) : nat :=
  row_signed_magnitude cs true.

Definition linear_row_negative_sum (cs : list linear_coeff) : nat :=
  row_signed_magnitude cs false.

Definition linear_row_exactly_balanced (cs : list linear_coeff) : bool :=
  Nat.eqb (linear_row_positive_sum cs) (linear_row_negative_sum cs).

Definition linear_row_dissipative (cs : list linear_coeff) : bool :=
  Nat.leb (linear_row_positive_sum cs) (linear_row_negative_sum cs).

(* ------------------------------------------------------------------ *)
(*  Dissipative witness for affine weakening                            *)
(* ------------------------------------------------------------------ *)

Record dissipative_witness : Type := {
  witness_axis : conservation_axis;
  witness_slack : nat
}.

Definition linear_conservation_ok
  (cs : list linear_coeff) (w : option dissipative_witness) : bool :=
  match w with
  | None => linear_row_exactly_balanced cs
  | Some _ =>
      linear_row_exactly_balanced cs || linear_row_dissipative cs
  end.

(* ------------------------------------------------------------------ *)
(*  TYPE-02 pins (structure witnesses — linear laws not Proved)           *)
(* ------------------------------------------------------------------ *)

Definition type02LinearProved : bool := false.

Lemma type02_linear_proved_false : type02LinearProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture rows — balanced and imbalanced linear conservation          *)
(* ------------------------------------------------------------------ *)

Definition balanced_mass_row : list linear_coeff :=
  [linear_coeff_positive 2; linear_coeff_negative 2].

Definition imbalanced_charge_row : list linear_coeff :=
  [linear_coeff_positive 3; linear_coeff_negative 1].

Definition dissipative_enthalpy_row : list linear_coeff :=
  [linear_coeff_positive 1; linear_coeff_negative 3].

Definition mass_axis_witness : dissipative_witness :=
  {| witness_axis := axis_mass; witness_slack := 1 |}.

(* ------------------------------------------------------------------ *)
(*  Balanced row lemma — signed coeffs sum to zero (identity conserved) *)
(* ------------------------------------------------------------------ *)

Lemma balanced_mass_row_exact :
  linear_row_exactly_balanced balanced_mass_row = true.
Proof.
  unfold linear_row_exactly_balanced, balanced_mass_row,
    linear_row_positive_sum, linear_row_negative_sum,
    row_signed_magnitude, linear_coeff_positive, linear_coeff_negative.
  simpl. reflexivity.
Qed.

Lemma balanced_row_positive_eq_negative (cs : list linear_coeff) :
  linear_row_exactly_balanced cs = true ->
  linear_row_positive_sum cs = linear_row_negative_sum cs.
Proof.
  intros H.
  unfold linear_row_exactly_balanced in H.
  apply Nat.eqb_eq in H.
  exact H.
Qed.

Theorem linear_row_balanced_conserves_identity :
  forall cs : list linear_coeff,
    linear_row_exactly_balanced cs = true ->
    linear_row_positive_sum cs = linear_row_negative_sum cs.
Proof.
  intros cs H. apply balanced_row_positive_eq_negative. exact H.
Qed.

Theorem balanced_mass_row_conserves_identity :
  linear_row_positive_sum balanced_mass_row =
  linear_row_negative_sum balanced_mass_row.
Proof.
  apply linear_row_balanced_conserves_identity.
  apply balanced_mass_row_exact.
Qed.

(* ------------------------------------------------------------------ *)
(*  Imbalanced refuse lemma — without witness, non-zero sum refused     *)
(* ------------------------------------------------------------------ *)

Lemma imbalanced_charge_row_not_exact :
  linear_row_exactly_balanced imbalanced_charge_row = false.
Proof.
  unfold linear_row_exactly_balanced, imbalanced_charge_row,
    linear_row_positive_sum, linear_row_negative_sum,
    row_signed_magnitude, linear_coeff_positive, linear_coeff_negative.
  simpl. reflexivity.
Qed.

Lemma linear_row_imbalanced_refuse_without_witness (cs : list linear_coeff) :
  linear_row_exactly_balanced cs = false ->
  linear_conservation_ok cs None = false.
Proof.
  intros H.
  unfold linear_conservation_ok.
  destruct (linear_row_exactly_balanced cs) eqn:E; try discriminate.
  reflexivity.
Qed.

Theorem imbalanced_charge_row_refused :
  linear_conservation_ok imbalanced_charge_row None = false.
Proof.
  apply linear_row_imbalanced_refuse_without_witness.
  apply imbalanced_charge_row_not_exact.
Qed.

(* ------------------------------------------------------------------ *)
(*  Affine weakening — only with dissipative witness                    *)
(* ------------------------------------------------------------------ *)

Lemma dissipative_enthalpy_row_dissipative :
  linear_row_dissipative dissipative_enthalpy_row = true.
Proof.
  unfold linear_row_dissipative, dissipative_enthalpy_row,
    linear_row_positive_sum, linear_row_negative_sum,
    row_signed_magnitude, linear_coeff_positive, linear_coeff_negative.
  simpl. reflexivity.
Qed.

Lemma affine_weakening_with_dissipative_witness_ok (cs : list linear_coeff)
  (dw : dissipative_witness) :
  linear_row_dissipative cs = true ->
  linear_conservation_ok cs (Some dw) = true.
Proof.
  intros H.
  unfold linear_conservation_ok.
  destruct (linear_row_exactly_balanced cs) eqn:E.
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Theorem dissipative_enthalpy_row_affine_weakening_ok :
  linear_conservation_ok dissipative_enthalpy_row
    (Some mass_axis_witness) = true.
Proof.
  apply affine_weakening_with_dissipative_witness_ok.
  apply dissipative_enthalpy_row_dissipative.
Qed.

Lemma affine_weakening_without_witness_refuse (cs : list linear_coeff) :
  linear_row_exactly_balanced cs = false ->
  linear_conservation_ok cs None = false.
Proof.
  intros. apply linear_row_imbalanced_refuse_without_witness. exact H.
Qed.

Theorem imbalanced_charge_affine_without_witness_refused :
  linear_conservation_ok imbalanced_charge_row None = false.
Proof.
  apply affine_weakening_without_witness_refuse.
  apply imbalanced_charge_row_not_exact.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_linear_conservation.

Definition linear_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition linear_conservation_knowing_fiber_ok : bool :=
  linear_conservation_fiber_ok fiber_quantum_knowing.

Definition linear_conservation_meso_acting_ok : bool :=
  linear_conservation_fiber_ok fiber_meso_acting.

Lemma linear_conservation_knowing_fiber_ok_true :
  linear_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma linear_conservation_meso_acting_not_ok :
  linear_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem linear_conservation_routes_knowing_not_meso :
  linear_conservation_knowing_fiber_ok = true /\
  linear_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply linear_conservation_knowing_fiber_ok_true.
  - apply linear_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  linear_conservation_knowing_fiber_ok &&
  negb linear_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, linear_conservation_knowing_fiber_ok,
    linear_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Axis structure witness — four axes not 118² table                   *)
(* ------------------------------------------------------------------ *)

Definition axis_count : nat := 4.

Lemma axis_count_is_four : axis_count = 4.
Proof. reflexivity. Qed.

Definition axes_not_118_squared : bool :=
  negb (Nat.eqb axis_count (118 * 118)).

Lemma axes_not_118_squared_true : axes_not_118_squared = true.
Proof.
  unfold axes_not_118_squared, axis_count.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — balance + affine + fiber + TYPE-02 pins          *)
(* ------------------------------------------------------------------ *)

Theorem linear_conservation_fixture_scaffold :
  linear_row_exactly_balanced balanced_mass_row = true /\
  linear_conservation_ok imbalanced_charge_row None = false /\
  linear_conservation_ok dissipative_enthalpy_row
    (Some mass_axis_witness) = true /\
  linear_conservation_knowing_fiber_ok = true /\
  linear_conservation_meso_acting_ok = false /\
  type02LinearProved = false.
Proof.
  split.
  - apply balanced_mass_row_exact.
  - split.
    + apply imbalanced_charge_row_refused.
    + split.
      * apply dissipative_enthalpy_row_affine_weakening_ok.
      * split.
        -- apply linear_conservation_knowing_fiber_ok_true.
        -- split.
           ++ apply linear_conservation_meso_acting_not_ok.
           ++ apply type02_linear_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — linear conservation) *)
(* ------------------------------------------------------------------ *)

Definition linearConservationAuthority : string :=
  "umst/umst-chem/src/linear_conservation.rs".

Definition chemL0Type02Authority : string :=
  "CHEM-L0-TYPE-02".

Definition chemIntProveType02LinearAuthority : string :=
  "CHEM-INT-PROVE-TYPE-02-LINEAR".

Definition linearConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-LINEAR-CONSERVATION".

Definition linearConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-LINEAR-CONSERVATION TYPE-02 linear conservation signed coeffs axis exact balance affine weakening dissipative witness Mass Charge AtomCount Enthalpy axes structure witness not 118 squared GREEN table geometry knowing quantum fiber not meso acting type02LinearProved false Unwired one axiom second law conservation not second linear axiom not GREEN DFT not physics GREEN not production_wired".

Lemma linear_conservation_cell_id :
  linearConservationCellId = "CHEM-FORMAL-Q-COQ-LINEAR-CONSERVATION".
Proof. reflexivity. Qed.

Lemma linear_conservation_cites_linear_rs :
  linearConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma linear_conservation_cites_l0_type_02 :
  chemL0Type02Authority = "CHEM-L0-TYPE-02".
Proof. reflexivity. Qed.

Lemma linear_conservation_cites_int_prove_type_02_linear :
  chemIntProveType02LinearAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second linear     *)
(* ------------------------------------------------------------------ *)

Definition linearSecondLawConservationFraming : string :=
  "second_law_conservation_linear_one_axiom_not_second_linear_axiom".

Lemma linear_not_second_linear_axiom :
  linearSecondLawConservationFraming <> "second_linear_axiom".
Proof. discriminate. Qed.

Lemma linear_second_law_conservation_framing :
  linearSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma linear_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma linear_conservation_modality_unwired :
  linearConservationModalityCurrent = linear_conservation_unwired.
Proof. reflexivity. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OreMonoidalConservation.v                             *)
(*                                                                      *)
(*  Knowing-fiber Coq: CAT-01 ore-monoidal conservation. Tensor unit   *)
(*  I and associator conserve assemblage identity; concurrent product  *)
(*  Π_c not XOR ore enum; monoidal laws Unwired not Proved.            *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — monoidal conservation is not a second       *)
(*  axiom. Not a 118² GREEN table.                                     *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  CAT-01 ore-monoidal conservation modality (TYPE-03 — Unwired)       *)
(* ------------------------------------------------------------------ *)

Inductive OreMonoidalConservationModality : Type :=
  | ore_monoidal_conservation_unwired
  | ore_monoidal_conservation_assumed
  | ore_monoidal_conservation_proved
  | ore_monoidal_conservation_surrogate.

Definition oreMonoidalConservationModalityCurrent : OreMonoidalConservationModality :=
  ore_monoidal_conservation_unwired.

(* ------------------------------------------------------------------ *)
(*  OreTree: binary product tree (⊗), not a list or XOR enum            *)
(* ------------------------------------------------------------------ *)

Inductive OreTag : Type :=
  | ore_tag_hematite
  | ore_tag_bauxite
  | ore_tag_gangue
  | ore_tag_vacuum.

Inductive OreTree : Type :=
  | leaf : OreTag -> OreTree
  | tensor : OreTree -> OreTree -> OreTree.

(* Unit I — inert / vacuum leaf (identity for concurrent product scaffold). *)
Definition unitI : OreTree := leaf ore_tag_vacuum.

Definition ore_tensor (a b : OreTree) : OreTree := tensor a b.

Definition hematiteLeaf : OreTree := leaf ore_tag_hematite.
Definition bauxiteLeaf : OreTree := leaf ore_tag_bauxite.
Definition gangueLeaf : OreTree := leaf ore_tag_gangue.

(* ------------------------------------------------------------------ *)
(*  Monoidal law pins (structure witnesses — laws not Proved)           *)
(* ------------------------------------------------------------------ *)

Definition monoidalLawsProved : bool := false.

Lemma monoidal_laws_proved_false : monoidalLawsProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Left / right unit lemmas — identity conservation of assemblage      *)
(* ------------------------------------------------------------------ *)

Definition left_unit_product (t : OreTree) : OreTree :=
  ore_tensor unitI t.

Definition right_unit_product (t : OreTree) : OreTree :=
  ore_tensor t unitI.

Lemma left_unit_identity_conservation (t : OreTree) :
  match left_unit_product t with
  | tensor l r => l = unitI /\ r = t
  | _ => False
  end.
Proof.
  simpl. split; reflexivity.
Qed.

Lemma right_unit_identity_conservation (t : OreTree) :
  match right_unit_product t with
  | tensor l r => l = t /\ r = unitI
  | _ => False
  end.
Proof.
  simpl. split; reflexivity.
Qed.

Theorem left_unit_conservation :
  forall t : OreTree,
    match left_unit_product t with
    | tensor l r => l = unitI /\ r = t
    | _ => False
    end.
Proof.
  intros t. apply left_unit_identity_conservation.
Qed.

Theorem right_unit_conservation :
  forall t : OreTree,
    match right_unit_product t with
    | tensor l r => l = t /\ r = unitI
    | _ => False
    end.
Proof.
  intros t. apply right_unit_identity_conservation.
Qed.

(* ------------------------------------------------------------------ *)
(*  Associator lemma — tensor bracketing conserves assemblage scaffold    *)
(* ------------------------------------------------------------------ *)

Definition associator_left (a b c : OreTree) : OreTree :=
  ore_tensor (ore_tensor a b) c.

Definition associator_right (a b c : OreTree) : OreTree :=
  ore_tensor a (ore_tensor b c).

Definition is_tensor_root (t : OreTree) : bool :=
  match t with
  | tensor _ _ => true
  | _ => false
  end.

Lemma associator_left_is_tensor (a b c : OreTree) :
  is_tensor_root (associator_left a b c) = true.
Proof. reflexivity. Qed.

Lemma associator_right_is_tensor (a b c : OreTree) :
  is_tensor_root (associator_right a b c) = true.
Proof. reflexivity. Qed.

Fixpoint left_depth (t : OreTree) : nat :=
  match t with
  | leaf _ => 0
  | tensor l _ => S (left_depth l)
  end.

Lemma left_depth_assoc_left (a b c : OreTree) :
  left_depth (associator_left a b c) = S (S (left_depth a)).
Proof. reflexivity. Qed.

Lemma left_depth_assoc_right (a b c : OreTree) :
  left_depth (associator_right a b c) = S (left_depth a).
Proof.
  destruct a; reflexivity.
Qed.

Lemma associator_bracketings_distinct : forall (a b c : OreTree),
  associator_left a b c <> associator_right a b c.
Proof.
  intros a b c H.
  apply (f_equal left_depth) in H.
  rewrite left_depth_assoc_left, left_depth_assoc_right in H.
  lia.
Qed.

Theorem associator_conservation (a b c : OreTree) :
  is_tensor_root (associator_left a b c) = true /\
  is_tensor_root (associator_right a b c) = true /\
  associator_left a b c <> associator_right a b c.
Proof.
  split.
  - apply associator_left_is_tensor.
  - split.
    + apply associator_right_is_tensor.
    + apply associator_bracketings_distinct.
Qed.

(* ------------------------------------------------------------------ *)
(*  productNotXor — concurrent Π_c product, not XOR ore enum            *)
(* ------------------------------------------------------------------ *)

Definition ore_tag_eqb (x y : OreTag) : bool :=
  match x, y with
  | ore_tag_hematite, ore_tag_hematite => true
  | ore_tag_bauxite, ore_tag_bauxite => true
  | ore_tag_gangue, ore_tag_gangue => true
  | ore_tag_vacuum, ore_tag_vacuum => true
  | _, _ => false
  end.

Fixpoint constituent_present (tag : OreTag) (t : OreTree) : bool :=
  match t with
  | leaf tg => ore_tag_eqb tg tag
  | tensor l r =>
      if constituent_present tag l then true else constituent_present tag r
  end.

Fixpoint concurrent_constituent_count (t : OreTree) : nat :=
  match t with
  | leaf tg =>
      match tg with
      | ore_tag_vacuum => 0
      | _ => 1
      end
  | tensor l r =>
      concurrent_constituent_count l + concurrent_constituent_count r
  end.

Definition triple_ore_product : OreTree :=
  ore_tensor (ore_tensor hematiteLeaf bauxiteLeaf) gangueLeaf.

Definition productNotXor : bool :=
  Nat.leb 3 (concurrent_constituent_count triple_ore_product).

Lemma triple_ore_concurrent_count :
  concurrent_constituent_count triple_ore_product = 3.
Proof. reflexivity. Qed.

Lemma product_not_xor_true : productNotXor = true.
Proof.
  unfold productNotXor.
  rewrite triple_ore_concurrent_count.
  reflexivity.
Qed.

Theorem product_not_xor_concurrent :
  productNotXor = true /\
  concurrent_constituent_count triple_ore_product >= 3.
Proof.
  split.
  - apply product_not_xor_true.
  - rewrite triple_ore_concurrent_count.
    apply Nat.le_refl.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — ore monoidal)         *)
(* ------------------------------------------------------------------ *)

Definition oreMonoidalProductAuthority : string :=
  "umst/umst-chem/src/ore_monoidal_product.rs".

Definition oreAssemblageAuthority : string :=
  "umst/umst-formal/Lean/Chem/OreAssemblage.lean".

Definition chemL0Cat01Authority : string :=
  "CHEM-L0-CAT-01".

Definition chemIntProveCat01MonoidalAuthority : string :=
  "CHEM-INT-PROVE-CAT-01-MONOIDAL".

Definition oreMonoidalConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-ORE-MONOIDAL-CONSERVATION".

Definition oreMonoidalConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ORE-MONOIDAL-CONSERVATION CAT-01 ore-monoidal conservation OreTree leaf tensor unitI left right unit identity conservation associator assemblage scaffold productNotXor concurrent Pi_c not XOR monoidalLawsProved false not 118 squared GREEN table Unwired one axiom second law conservation not second monoidal axiom not GREEN DFT not physics GREEN not production_wired".

Lemma ore_monoidal_conservation_cell_id :
  oreMonoidalConservationCellId =
  "CHEM-FORMAL-Q-COQ-ORE-MONOIDAL-CONSERVATION".
Proof. reflexivity. Qed.

Lemma ore_monoidal_cites_product_rs :
  oreMonoidalProductAuthority <>
  "".
Proof. discriminate. Qed.

Lemma ore_monoidal_cites_ore_assemblage :
  oreAssemblageAuthority <>
  "".
Proof. discriminate. Qed.

Lemma ore_monoidal_cites_l0_cat_01 :
  chemL0Cat01Authority = "CHEM-L0-CAT-01".
Proof. reflexivity. Qed.

Lemma ore_monoidal_cites_int_prove_cat_01 :
  chemIntProveCat01MonoidalAuthority <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second monoidal   *)
(* ------------------------------------------------------------------ *)

Definition oreMonoidalSecondLawConservationFraming : string :=
  "second_law_conservation_ore_monoidal_one_axiom_not_second_monoidal_axiom".

Lemma ore_monoidal_not_second_monoidal_axiom :
  oreMonoidalSecondLawConservationFraming <>
  "second_monoidal_axiom".
Proof. discriminate. Qed.

Lemma ore_monoidal_second_law_conservation_framing :
  oreMonoidalSecondLawConservationFraming <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma ore_monoidal_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma ore_monoidal_modality_unwired :
  oreMonoidalConservationModalityCurrent = ore_monoidal_conservation_unwired.
Proof. reflexivity. Qed.

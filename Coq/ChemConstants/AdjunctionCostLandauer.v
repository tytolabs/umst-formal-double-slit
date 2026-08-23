(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AdjunctionCostLandauer.v                              *)
(*                                                                      *)
(*  Knowing-fiber Coq: CAT-03 adjunction-cost Landauer.                 *)
(*  Pureward refine cost non-negative; free purification forbidden.     *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — Landauer cost is not a second axiom.         *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  CAT-03 adjunction-cost modality (TYPE-03 preview — Unwired)        *)
(* ------------------------------------------------------------------ *)

Inductive AdjunctionCostLandauerModality : Type :=
  | adjunction_cost_landauer_unwired
  | adjunction_cost_landauer_assumed
  | adjunction_cost_landauer_proved
  | adjunction_cost_landauer_surrogate.

Definition adjunctionCostLandauerModalityCurrent : AdjunctionCostLandauerModality :=
  adjunction_cost_landauer_unwired.

(* ------------------------------------------------------------------ *)
(*  Pureward cost pins (knowing fiber — Unwired)                        *)
(* ------------------------------------------------------------------ *)

Definition purewardCost : nat := 1.

Definition contaminantsPresent : bool := true.

Definition minPurewardCost (hasContaminants : bool) : nat :=
  if hasContaminants then purewardCost else 0.

Lemma pureward_cost_positive : 0 < purewardCost.
Proof. unfold purewardCost. apply Nat.lt_0_succ. Qed.

Lemma pureward_cost_nonneg : 0 <= purewardCost.
Proof. apply Nat.le_0_l. Qed.

Lemma min_pureward_cost_nonneg (hasContaminants : bool) :
  0 <= minPurewardCost hasContaminants.
Proof.
  unfold minPurewardCost.
  destruct hasContaminants; simpl.
  - apply pureward_cost_nonneg.
  - apply Nat.le_0_l.
Qed.

Lemma min_pureward_cost_zero_when_pure :
  minPurewardCost false = 0.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification fence (cost 0 refused when contaminants remain)    *)
(* ------------------------------------------------------------------ *)

Definition freePurificationAdmitted
  (paidCost minCost : nat) (hasContaminants : bool) : bool :=
  if hasContaminants then Nat.leb minCost paidCost else true.

Definition attemptZeroCostPurification (hasContaminants : bool) : bool :=
  freePurificationAdmitted 0 (minPurewardCost hasContaminants) hasContaminants.

Lemma free_purification_admitted_false_when_impure :
  attemptZeroCostPurification true = false.
Proof.
  unfold attemptZeroCostPurification, freePurificationAdmitted, minPurewardCost.
  simpl. reflexivity.
Qed.

Theorem freePurificationForbidden :
  attemptZeroCostPurification true = false.
Proof. apply free_purification_admitted_false_when_impure. Qed.

Lemma free_purification_admitted_true_when_pure :
  attemptZeroCostPurification false = true.
Proof.
  unfold attemptZeroCostPurification, freePurificationAdmitted, minPurewardCost.
  simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Purification with contaminants implies positive minimum cost         *)
(* ------------------------------------------------------------------ *)

Lemma purificationImpliesPositiveCost :
  minPurewardCost true > 0.
Proof.
  unfold minPurewardCost.
  simpl.
  apply pureward_cost_positive.
Qed.

Lemma paid_pureward_cost_admits_purification :
  freePurificationAdmitted purewardCost (minPurewardCost true) true = true.
Proof.
  unfold freePurificationAdmitted, minPurewardCost.
  simpl. reflexivity.
Qed.

Theorem adjunction_cost_paid_pureward_admits :
  freePurificationAdmitted purewardCost (minPurewardCost true) true = true /\
  attemptZeroCostPurification true = false.
Proof.
  split.
  - apply paid_pureward_cost_admits_purification.
  - apply freePurificationForbidden.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — adjunction cost)      *)
(* ------------------------------------------------------------------ *)

Definition impurePureAdjunctionAuthority : string :=
  "umst/umst-chem/src/impure_pure_adjunction.rs".

Definition chemL0Cat03Authority : string :=
  "CHEM-L0-CAT-03".

Definition refineCostAuthority : string :=
  "umst/umst-formal/Lean/Chem/RefineCost.lean".

Definition adjunctionCostLandauerCellId : string :=
  "CHEM-FORMAL-Q-COQ-ADJUNCTION-COST-LANDAUER".

Definition adjunctionCostLandauerNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ADJUNCTION-COST-LANDAUER CAT-03 adjunction-cost Landauer purewardCost mandatory freePurificationForbidden contaminantsPresent Unwired one axiom second law conservation Landauer cost not second axiom not GREEN DFT not physics GREEN not production_wired".

Lemma adjunction_cost_landauer_cell_id :
  adjunctionCostLandauerCellId =
  "CHEM-FORMAL-Q-COQ-ADJUNCTION-COST-LANDAUER".
Proof. reflexivity. Qed.

Lemma adjunction_cost_cites_impure_pure_adjunction :
  impurePureAdjunctionAuthority <>
  "".
Proof. discriminate. Qed.

Lemma adjunction_cost_cites_l0_cat_03 :
  chemL0Cat03Authority = "CHEM-L0-CAT-03".
Proof. reflexivity. Qed.

Lemma adjunction_cost_cites_refine_cost :
  refineCostAuthority <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer    *)
(* ------------------------------------------------------------------ *)

Definition adjunctionSecondLawConservationFraming : string :=
  "second_law_conservation_adjunction_cost_one_axiom_landauer_not_second_axiom".

Lemma adjunction_not_second_landauer_axiom :
  adjunctionSecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma adjunction_second_law_conservation_framing :
  adjunctionSecondLawConservationFraming <>
  "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma adjunction_cost_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma adjunction_cost_modality_unwired :
  adjunctionCostLandauerModalityCurrent = adjunction_cost_landauer_unwired.
Proof. reflexivity. Qed.

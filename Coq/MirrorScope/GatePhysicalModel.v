(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* P0-13b: constitutive laws as a Record (mirror Agda MirrorScope.GatePhysicalModel). *)

From Coq Require Import QArith.
From UMSTFormal Require Import Gate.

Open Scope Q_scope.

Record GatePhysicalLaws : Set := {
  psi_antitone_law :
    forall s1 s2 : ThermodynamicState,
      hydration s1 <= hydration s2 ->
      free_energy s2 <= free_energy s1;
  fc_monotone_law :
    forall s1 s2 : ThermodynamicState,
      hydration s1 <= hydration s2 ->
      strength s1 <= strength s2
}.

Section WithPhysicalLaws.
  Variable L : GatePhysicalLaws.

  Definition psi_antitone :=
    psi_antitone_law L.
  Definition fc_monotone :=
    fc_monotone_law L.

  Theorem clausius_duhem_forward :
    forall s1 s2 : ThermodynamicState,
    hydration s1 <= hydration s2 ->
    free_energy s2 <= free_energy s1.
  Proof.
    intros s1 s2 Hhyd.
    exact (psi_antitone s1 s2 Hhyd).
  Qed.

  Theorem strength_monotone_powers :
    forall s1 s2 : ThermodynamicState,
    hydration s1 <= hydration s2 ->
    strength s1 <= strength s2.
  Proof.
    intros s1 s2 Hhyd.
    exact (fc_monotone s1 s2 Hhyd).
  Qed.

  Theorem forward_hydration_admissible :
    forall old new_ : ThermodynamicState,
    hydration old <= hydration new_ ->
    density new_ - density old <= delta_mass ->
    density old - density new_ <= delta_mass ->
    admissible old new_.
  Proof.
    intros old new_ Hhyd Hmc1 Hmc2.
    unfold admissible.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    - exact Hmc1.
    - exact Hmc2.
    - exact (psi_antitone old new_ Hhyd).
    - exact Hhyd.
    - exact (fc_monotone old new_ Hhyd).
  Qed.

  Corollary gate_accepts_forward_hydration :
    forall old new_ : ThermodynamicState,
    hydration old <= hydration new_ ->
    density new_ - density old <= delta_mass ->
    density old - density new_ <= delta_mass ->
    gate_check old new_ = true.
  Proof.
    intros old new_ Hhyd Hmc1 Hmc2.
    apply gate_check_complete.
    exact (forward_hydration_admissible old new_ Hhyd Hmc1 Hmc2).
  Qed.

  Print Assumptions forward_hydration_admissible.

End WithPhysicalLaws.

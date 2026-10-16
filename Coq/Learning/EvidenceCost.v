(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal-Double-Slit: Learning/EvidenceCost.v                      *)
(*                                                                        *)
(*  Twin of Lean/Learning/EvidenceCost.lean: a verification is an         *)
(*  observation whose record is paid for when it is reset. A record of    *)
(*  b evidence bits (the uniform distribution on 2^b states, b ln 2 nats, *)
(*  carried as the entropy the erase case removes) costs at least         *)
(*  b k_B T ln 2, so evidence bits per joule are at most 1/(k_B T ln 2);  *)
(*  on the path qubit the same rate holds for the path-entropy bits, and  *)
(*  the reset costs at least the larger of the Landauer and the Englert   *)
(*  bound.                                                                *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.
From UMSTFormal Require Import DensityStateSpec ComplementaritySpec KnowingFibreLaw.

Open Scope R_scope.

(** The erase case on a record of [bits] evidence bits: the b ln 2 nats it holds are at most W / T. *)
Definition bitsEraseCase (e : ErasureProcess) (bits : R) : Prop :=
  bits * ln 2 <= work e / bathTemp (erasureBath e).

Lemma landauerBitEnergy_pos' (T : R) : 0 < T -> 0 < landauerBitEnergy T.
Proof. intro hT. unfold landauerBitEnergy. pose proof kB_pos. pose proof ln2_pos. apply Rmult_lt_0_compat; [nra | lra]. Qed.

(** Each evidence bit costs at least k_B T ln 2. *)
Theorem evidenceBits_cost_ge (e : ErasureProcess) (bits : R) :
  bitsEraseCase e bits -> bits * landauerBitEnergy (bathTemp (erasureBath e)) <= kB * work e.
Proof.
  unfold bitsEraseCase, landauerBitEnergy. intro h.
  pose proof (bathTemp_pos (erasureBath e)) as hT. pose proof kB_pos as hk.
  apply (Rmult_le_compat_r (bathTemp (erasureBath e))) in h; [| lra].
  replace (work e / bathTemp (erasureBath e) * bathTemp (erasureBath e)) with (work e) in h by (field; lra).
  apply (Rmult_le_compat_l kB) in h; [| lra]. nra.
Qed.

(** Evidence per joule is bounded. *)
Theorem evidenceBitsPerJoule_le (e : ErasureProcess) (bits : R) :
  0 < work e -> bitsEraseCase e bits -> bits / (kB * work e) <= 1 / landauerBitEnergy (bathTemp (erasureBath e)).
Proof.
  intros hW h. pose proof (evidenceBits_cost_ge e bits h) as hc.
  pose proof (landauerBitEnergy_pos' _ (bathTemp_pos (erasureBath e))) as hL. pose proof kB_pos as hk.
  assert (hkW : 0 < kB * work e) by nra.
  apply (Rmult_le_reg_r (kB * work e * landauerBitEnergy (bathTemp (erasureBath e)))); [nra |].
  replace (bits / (kB * work e) * (kB * work e * landauerBitEnergy (bathTemp (erasureBath e))))
    with (bits * landauerBitEnergy (bathTemp (erasureBath e))) by (field; lra).
  replace (1 / landauerBitEnergy (bathTemp (erasureBath e)) * (kB * work e * landauerBitEnergy (bathTemp (erasureBath e))))
    with (kB * work e) by (field; lra).
  exact hc.
Qed.

(** On the path qubit: path-entropy bits per joule are at most 1/(k_B T ln 2). *)
Theorem pathEvidencePerJoule_le (e : ErasureProcess) (rho : DensityMatrix2) :
  0 < work e -> eraseCase e (pathBornDist rho) ->
  pathEntropyBits rho / (kB * work e) <= 1 / landauerBitEnergy (bathTemp (erasureBath e)).
Proof.
  intros hW h. pose proof (erase_pathRecord_cost_ge_bits e rho h) as hc.
  pose proof (landauerBitEnergy_pos' _ (bathTemp_pos (erasureBath e))) as hL. pose proof kB_pos as hk.
  assert (hkW : 0 < kB * work e) by nra.
  apply (Rmult_le_reg_r (kB * work e * landauerBitEnergy (bathTemp (erasureBath e)))); [nra |].
  replace (pathEntropyBits rho / (kB * work e) * (kB * work e * landauerBitEnergy (bathTemp (erasureBath e))))
    with (landauerBitEnergy (bathTemp (erasureBath e)) * pathEntropyBits rho) by (field; lra).
  replace (1 / landauerBitEnergy (bathTemp (erasureBath e)) * (kB * work e * landauerBitEnergy (bathTemp (erasureBath e))))
    with (kB * work e) by (field; lra).
  exact hc.
Qed.

(** Landauer and Englert together: the reset costs at least the larger of the two bounds. *)
Theorem pathEvidence_cost_ge_max (e : ErasureProcess) (rho : DensityMatrix2) :
  eraseCase e (pathBornDist rho) ->
  Rmax (landauerBitEnergy (bathTemp (erasureBath e)) * pathEntropyBits rho)
       (kB * bathTemp (erasureBath e) * (visibility rho * visibility rho) / 2) <= kB * work e.
Proof.
  intro h. apply Rmax_lub; [exact (erase_pathRecord_cost_ge_bits e rho h) | exact (erase_pathRecord_cost_ge_visibility_sq e rho h)].
Qed.

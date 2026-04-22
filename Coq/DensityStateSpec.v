(* SPDX-License-Identifier: MIT *)
(* Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO *)

(* ================================================================== *)
(*  UMST-Formal: DensityStateSpec.v                                    *)
(*                                                                      *)
(*  Spec-level port of Lean/DensityState.lean to Coq.                  *)
(*                                                                      *)
(*  A 2x2 density matrix is represented as a record of its four        *)
(*  real parameters (p0, p1 on the diagonal; rho01_re, rho01_im        *)
(*  off-diagonal) together with proofs of the quantum-mechanical       *)
(*  constraints:                                                        *)
(*    - non-negative diagonal entries                                   *)
(*    - trace = 1                                                       *)
(*    - positive semidefiniteness (det >= 0)                            *)
(*                                                                      *)
(*  Proved:                                                             *)
(*    - p0_le_one, p1_le_one  (diagonal entries <= 1)                  *)
(*    - coherence_bounded     (|rho01|^2 <= p0 * p1)                   *)
(* ================================================================== *)

From Coq Require Import Reals Lra RIneq.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  2x2 density matrix record                                          *)
(* ------------------------------------------------------------------ *)

(** A qubit density matrix parameterised by its four real degrees of
    freedom.  The off-diagonal element is rho01 = rho01_re + i rho01_im;
    Hermiticity forces rho10 = conj(rho01).

    The [psd] field encodes det(rho) >= 0, which for a 2x2 Hermitian
    matrix with non-negative diagonal and unit trace is equivalent to
    positive semidefiniteness. *)
Record DensityMatrix2 : Type := mkDensityMatrix2 {
  p0       : R;    (** diagonal element [0,0] *)
  p1       : R;    (** diagonal element [1,1] *)
  rho01_re : R;    (** Re(rho_{01}) *)
  rho01_im : R;    (** Im(rho_{01}) *)

  p0_nonneg : 0 <= p0;
  p1_nonneg : 0 <= p1;
  trace_one : p0 + p1 = 1;
  psd       : p0 * p1 >= rho01_re * rho01_re + rho01_im * rho01_im
}.

(* ------------------------------------------------------------------ *)
(*  Proved lemmas                                                       *)
(* ------------------------------------------------------------------ *)

(** Each diagonal entry is at most 1 (from trace = 1 and non-negativity
    of the other entry). *)
Lemma p0_le_one (rho : DensityMatrix2) : p0 rho <= 1.
Proof.
  pose proof (p1_nonneg rho).
  pose proof (trace_one rho).
  lra.
Qed.

Lemma p1_le_one (rho : DensityMatrix2) : p1 rho <= 1.
Proof.
  pose proof (p0_nonneg rho).
  pose proof (trace_one rho).
  lra.
Qed.

(** Off-diagonal coherence is bounded by the product of the diagonal
    entries.  This is the 2x2 PSD principal-minor condition and
    corresponds to [normSq_coherence_le_product] in the Lean codebase. *)
Lemma coherence_bounded (rho : DensityMatrix2) :
  rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho <= p0 rho * p1 rho.
Proof.
  pose proof (psd rho).
  lra.
Qed.

(** The off-diagonal modulus squared is non-negative (trivial but useful
    as a building block). *)
Lemma coherence_sq_nonneg (rho : DensityMatrix2) :
  0 <= rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho.
Proof.
  assert (H1 : 0 <= rho01_re rho * rho01_re rho) by (apply Rle_0_sqr).
  assert (H2 : 0 <= rho01_im rho * rho01_im rho) by (apply Rle_0_sqr).
  lra.
Qed.

(** The product p0 * p1 is non-negative. *)
Lemma p0_p1_nonneg (rho : DensityMatrix2) : 0 <= p0 rho * p1 rho.
Proof.
  apply Rmult_le_pos; [exact (p0_nonneg rho) | exact (p1_nonneg rho)].
Qed.

(** The product p0 * p1 is at most 1/4 (AM-GM with p0 + p1 = 1). *)
Lemma p0_p1_le_quarter (rho : DensityMatrix2) : p0 rho * p1 rho <= 1 / 4.
Proof.
  pose proof (trace_one rho) as Htr.
  pose proof (p0_nonneg rho) as Hp0.
  pose proof (p1_nonneg rho) as Hp1.
  assert (Hexp : (p0 rho + p1 rho) * (p0 rho + p1 rho) =
               (p0 rho - p1 rho) * (p0 rho - p1 rho) + 4 * (p0 rho * p1 rho)) by ring.
  rewrite Htr in Hexp.
  assert (Hnonneg : 0 <= (p0 rho - p1 rho) * (p0 rho - p1 rho)).
  { destruct (Rle_dec 0 (p0 rho - p1 rho)) as [Hge|Hlt].
    - apply Rmult_le_pos; [exact Hge | exact Hge].
    - replace ((p0 rho - p1 rho) * (p0 rho - p1 rho))
        with ((p1 rho - p0 rho) * (p1 rho - p0 rho)) by ring.
      assert (Hg : 0 <= p1 rho - p0 rho) by lra.
      apply Rmult_le_pos; [exact Hg | exact Hg]. }
  assert (H4bound : 4 * (p0 rho * p1 rho) <= 1) by lra.
  lra.
Qed.

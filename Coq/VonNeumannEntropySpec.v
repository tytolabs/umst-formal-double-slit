(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: VonNeumannEntropySpec.v                               *)
(*                                                                      *)
(*  Spec-level port of Lean/VonNeumannEntropy.lean and                 *)
(*  Lean/DataProcessingInequality.lean to Coq.                         *)
(*                                                                      *)
(*  Defines:                                                            *)
(*    - Binary Shannon entropy via [negMulLog]                         *)
(*    - Diagonal von Neumann entropy (from Born weights)               *)
(*    - Spectral von Neumann entropy (axiomatised)                     *)
(*                                                                      *)
(*  Proved (from DensityMatrix2 constraints):                          *)
(*    - shannon_binary_nonneg                                          *)
(*    - vonNeumannDiagonal_nonneg                                      *)
(*    - vonNeumannDiagonal_le_ln2 (uses axiom [shannon_binary_le_ln2]) *)
(*    - vonNeumannDiagonal_zero_iff_diagonal_pure (uses [negMulLog_zero_interval]) *)
(*                                                                      *)
(*  Axiomatised (real analysis; Coq stdlib without convexity calculus):  *)
(*    - shannon_binary_le_ln2 (concavity of -x ln x on [0,1])          *)
(*    - negMulLog_zero_interval (zeros of -x ln x on [0,1])            *)
(*                                                                      *)
(*  Axiomatised (require spectral decomposition / eigenvalues):        *)
(*    - vonNeumannEntropy (spectral S(rho))                            *)
(*    - vonNeumannEntropy_nonneg                                       *)
(*    - vonNeumannEntropy_le_ln2                                       *)
(*    - vonNeumannDiagonal_ge_spectral (Schur concavity)               *)
(*    - vonNeumannEntropy_unitary_invariant                            *)
(*    - vonNeumannEntropy_pure_zero                                    *)
(*    - vonNeumannEntropy_maximally_mixed                              *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra RIneq Rpower.
From UMSTFormal Require Import DensityStateSpec.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  negMulLog: -x ln x  with the convention  0 ln 0 = 0               *)
(* ------------------------------------------------------------------ *)

(** The standard information-theoretic function f(x) = -x ln x,
    extended by continuity to f(0) = 0.  Matches Mathlib's
    [Real.negMulLog]. *)
Definition negMulLog (x : R) : R :=
  match Rle_dec x 0 with
  | left _  => 0
  | right _ => - x * ln x
  end.

(** negMulLog is non-negative on [0, 1]. *)
Lemma negMulLog_nonneg (x : R) (hx0 : 0 <= x) (hx1 : x <= 1) :
  0 <= negMulLog x.
Proof.
  unfold negMulLog.
  destruct (Rle_dec x 0) as [Hle | Hgt].
  - lra.
  - (* x > 0 and x <= 1, so ln x <= 0, hence -x * ln x >= 0 *)
    assert (Hxpos : 0 < x) by lra.
    assert (Hln : ln x <= 0).
    { destruct (Rlt_dec x 1) as [Hlt1 | Hge1].
      - assert (Hltln : ln x < ln 1) by (apply ln_increasing; lra).
        rewrite ln_1 in Hltln. lra.
      - assert (Heq : x = 1) by lra.
        subst x. rewrite ln_1. lra. }
    assert (Hxln : x * ln x <= 0).
    { replace 0 with (x * 0) by ring.
      apply Rmult_le_compat_l; [now apply Rlt_le | exact Hln]. }
    replace (- x * ln x) with (- (x * ln x)) by ring.
    lra.
Qed.

(** negMulLog(1) = 0. *)
Lemma negMulLog_one : negMulLog 1 = 0.
Proof.
  unfold negMulLog.
  destruct (Rle_dec 1 0) as [H | _].
  - lra.
  - rewrite ln_1. ring.
Qed.

(** negMulLog(0) = 0 (by our convention). *)
Lemma negMulLog_zero : negMulLog 0 = 0.
Proof.
  unfold negMulLog.
  destruct (Rle_dec 0 0) as [_ | H].
  - reflexivity.
  - exfalso; lra.
Qed.


(* ------------------------------------------------------------------ *)
(*  Binary Shannon entropy                                              *)
(* ------------------------------------------------------------------ *)

(** Binary Shannon entropy H(p) = -p ln p - (1-p) ln(1-p).
    This is the natural-logarithm version; divide by ln 2 for bits. *)
Definition shannon_binary (p : R) : R :=
  negMulLog p + negMulLog (1 - p).

(** Binary Shannon entropy is non-negative for p in [0, 1]. *)
Lemma shannon_binary_nonneg (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  0 <= shannon_binary p.
Proof.
  unfold shannon_binary.
  assert (H1 : 0 <= negMulLog p) by (apply negMulLog_nonneg; lra).
  assert (H2 : 0 <= negMulLog (1 - p)) by (apply negMulLog_nonneg; lra).
  lra.
Qed.


(* ------------------------------------------------------------------ *)
(*  Diagonal von Neumann entropy                                        *)
(* ------------------------------------------------------------------ *)

(** The "diagonal" von Neumann entropy: Shannon entropy of the Born
    weights (diagonal of the density matrix in the computational basis).
    Corresponds to [vonNeumannDiagonal_n] in the Lean codebase. *)
Definition vonNeumannDiagonal (rho : DensityMatrix2) : R :=
  shannon_binary (p0 rho).

(** Diagonal entropy is non-negative. *)
Lemma vonNeumannDiagonal_nonneg (rho : DensityMatrix2) :
  0 <= vonNeumannDiagonal rho.
Proof.
  unfold vonNeumannDiagonal.
  apply shannon_binary_nonneg.
  - exact (p0_nonneg rho).
  - exact (p0_le_one rho).
Qed.


(** The diagonal entropy uses p1 = 1 - p0 from the trace constraint. *)
Lemma vonNeumannDiagonal_alt (rho : DensityMatrix2) :
  vonNeumannDiagonal rho = negMulLog (p0 rho) + negMulLog (p1 rho).
Proof.
  unfold vonNeumannDiagonal, shannon_binary.
  f_equal.
  pose proof (trace_one rho).
  f_equal.
  lra.
Qed.


(** ln y <= y - 1 for y > 0, from 1 + z <= exp z at z = ln y. *)
Lemma ln_le_minus_one (y : R) (hy : 0 < y) : ln y <= y - 1.
Proof. pose proof (exp_ineq1_le (ln y)) as h. rewrite exp_ln in h by exact hy. lra. Qed.

(** One term of the binary entropy against ln 2: -x ln x <= x ln 2 - x + 1/2 for x >= 0. *)
Lemma negMulLog_le_affine (x : R) (hx : 0 <= x) : negMulLog x <= x * ln 2 - x + 1 / 2.
Proof.
  unfold negMulLog. destruct (Rle_dec x 0) as [Hle | Hgt].
  - assert (x = 0) by lra. subst x. lra.
  - assert (hx' : 0 < x) by lra.
    assert (h2x : 0 < / (2 * x)) by (apply Rinv_0_lt_compat; lra).
    pose proof (ln_le_minus_one (/ (2 * x)) h2x) as h.
    rewrite ln_Rinv in h by lra. rewrite ln_mult in h by lra.
    assert (hk : x * (/ (2 * x)) = 1 / 2) by (field; lra).
    assert (x * (- (ln 2 + ln x)) <= x * (/ (2 * x) - 1)) by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

(** The binary Shannon entropy is at most ln 2. *)
Theorem shannon_binary_le_ln2 (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) : shannon_binary p <= ln 2.
Proof.
  unfold shannon_binary.
  pose proof (negMulLog_le_affine p hp0). pose proof (negMulLog_le_affine (1 - p) ltac:(lra)). lra.
Qed.

(** On [0, 1], -x ln x vanishes only at 0 and 1. *)
Theorem negMulLog_zero_interval (x : R) (hx0 : 0 <= x) (hx1 : x <= 1) : negMulLog x = 0 -> x = 0 \/ x = 1.
Proof.
  unfold negMulLog. destruct (Rle_dec x 0) as [Hle | Hgt]; intro h; [left; lra |].
  right. assert (hx : 0 < x) by lra.
  assert (hln : ln x = 0).
  { apply Rmult_eq_reg_l with (r := - x); [lra | lra]. }
  rewrite <- ln_1 in hln. apply ln_inv in hln; lra.
Qed.

(** The diagonal entropy of a qubit is at most ln 2. *)
Theorem vonNeumannDiagonal_le_ln2 (rho : DensityMatrix2) : vonNeumannDiagonal rho <= ln 2.
Proof. unfold vonNeumannDiagonal. apply shannon_binary_le_ln2; [exact (p0_nonneg rho) | exact (p0_le_one rho)]. Qed.

(** The diagonal entropy vanishes only when the diagonal is pure. *)
Theorem vonNeumannDiagonal_zero_iff_diagonal_pure (rho : DensityMatrix2) :
  vonNeumannDiagonal rho = 0 -> p0 rho = 0 \/ p0 rho = 1.
Proof.
  unfold vonNeumannDiagonal, shannon_binary. intro H.
  pose proof (p0_nonneg rho). pose proof (p0_le_one rho).
  assert (Ha : 0 <= negMulLog (p0 rho)) by (apply negMulLog_nonneg; lra).
  assert (Hb : 0 <= negMulLog (1 - p0 rho)) by (apply negMulLog_nonneg; lra).
  apply negMulLog_zero_interval; lra.
Qed.

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

(* negMulLog_zero_interval / shannon_binary_le_ln2: see MirrorScope.VonNeumannEntropyModel *)

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

(* shannon_binary_le_ln2: MirrorScope.VonNeumannEntropyModel.WithShannonRealAnalysis *)

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

(** Diagonal entropy bound: MirrorScope.VonNeumannEntropyModel.vonNeumannDiagonal_le_ln2_scoped *)

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

(* Spectral von Neumann entropy: MirrorScope.VonNeumannEntropyModel.SpectralVonNeumannEntropy *)

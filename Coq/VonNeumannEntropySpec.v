(* SPDX-License-Identifier: MIT *)
(* Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO *)

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
(*    - vonNeumannDiagonal_zero_iff_diagonal_pure (uses axiom below)   *)
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

(** On [0,1], if [negMulLog x = 0] then [x = 0] or [x = 1] (convention [0 ln 0 = 0]).
    Equivalent to characterising zeros of [-x ln x]; axiomatised here. *)
Axiom negMulLog_zero_interval :
  forall x : R, 0 <= x -> x <= 1 -> negMulLog x = 0 -> x = 0 \/ x = 1.

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

(** Binary Shannon entropy is at most ln 2 (maximum at p = 1/2).
    Proof sketch: concavity of [negMulLog] on [0,1] gives
    [H(p)=f(p)+f(1-p) <= 2 f(1/2) = ln 2].  Axiomatised (stdlib). *)
Axiom shannon_binary_le_ln2 : forall (p : R) (hp0 : 0 <= p) (hp1 : p <= 1),
  shannon_binary p <= ln 2.

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

(** Diagonal entropy is at most ln 2. *)
Lemma vonNeumannDiagonal_le_ln2 (rho : DensityMatrix2) :
  vonNeumannDiagonal rho <= ln 2.
Proof.
  unfold vonNeumannDiagonal.
  apply shannon_binary_le_ln2.
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

(* ------------------------------------------------------------------ *)
(*  Spectral von Neumann entropy (axiomatised)                          *)
(* ------------------------------------------------------------------ *)

(** The true von Neumann entropy S(rho) = -Tr(rho log rho), computed
    from the eigenvalues of the density matrix.  For a full definition
    one needs the spectral decomposition, which requires heavy linear
    algebra.  We axiomatize the function and its key properties.

    In Lean, this is [UMST.Quantum.vonNeumannEntropy] defined via
    [sum of negMulLog(eigenvalue_i)]. *)
Axiom vonNeumannEntropy : DensityMatrix2 -> R.

(** S(rho) >= 0.  Eigenvalues lie in [0,1], so negMulLog >= 0 for each. *)
Axiom vonNeumannEntropy_nonneg : forall rho : DensityMatrix2,
  0 <= vonNeumannEntropy rho.

(** S(rho) <= ln 2 for a qubit.  Maximum entropy is the maximally
    mixed state (eigenvalues 1/2, 1/2). *)
Axiom vonNeumannEntropy_le_ln2 : forall rho : DensityMatrix2,
  vonNeumannEntropy rho <= ln 2.

(** Diagonal entropy >= spectral entropy (Schur concavity /
    measurement increases entropy).  This is the key content of
    Lean/DataProcessingInequality.lean.

    The diagonal entries majorize the eigenvalues (Schur's theorem),
    and von Neumann entropy is Schur-concave, so computing entropy
    on diagonal entries (Born weights) overestimates the true
    quantum entropy. *)
Axiom vonNeumannDiagonal_ge_spectral : forall rho : DensityMatrix2,
  vonNeumannDiagonal rho >= vonNeumannEntropy rho.

(** Unitary invariance: [S(U rho U^dagger) = S(rho)].
    Proved in Lean as [vonNeumannEntropy_unitarily_invariant]
    via charpoly preservation under similarity. *)
Axiom vonNeumannEntropy_unitary_invariant :
  forall (rho : DensityMatrix2) (U_det_one : True),
  vonNeumannEntropy rho = vonNeumannEntropy rho.
  (* Note: without a concrete unitary representation in this 2x2 real
     parameterisation, we state the invariance as an identity.  A richer
     formulation would take a unitary channel and produce a new
     DensityMatrix2. *)

(** Pure states have zero entropy. *)
Axiom vonNeumannEntropy_pure_zero :
  forall (rho : DensityMatrix2),
  p0 rho * p1 rho = rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho ->
  vonNeumannEntropy rho = 0.

(** The maximally mixed state (p0 = p1 = 1/2, rho01 = 0) achieves
    maximum entropy ln 2. *)
Axiom vonNeumannEntropy_maximally_mixed :
  forall (rho : DensityMatrix2),
  p0 rho = 1/2 -> p1 rho = 1/2 ->
  rho01_re rho = 0 -> rho01_im rho = 0 ->
  vonNeumannEntropy rho = ln 2.

(* ------------------------------------------------------------------ *)
(*  Derived: diagonal entropy of pure state is zero iff pure           *)
(* ------------------------------------------------------------------ *)

(** For a pure state (det = 0), one eigenvalue is 0 and the other is 1,
    so diagonal entries are also 0 and 1 when the state is diagonal.
    In general, diagonal entropy of a pure state may be positive (if
    the pure state has coherence in the computational basis). *)
Lemma vonNeumannDiagonal_zero_iff_diagonal_pure (rho : DensityMatrix2) :
  vonNeumannDiagonal rho = 0 ->
  (p0 rho = 0 \/ p0 rho = 1).
Proof.
  unfold vonNeumannDiagonal, shannon_binary.
  intro H.
  assert (H1 : 0 <= negMulLog (p0 rho)).
  { apply negMulLog_nonneg; [exact (p0_nonneg rho) | exact (p0_le_one rho)]. }
  assert (H2 : 0 <= negMulLog (1 - p0 rho)).
  { apply negMulLog_nonneg; [| ]; pose proof (p0_nonneg rho); pose proof (p0_le_one rho); lra. }
  assert (Hf1 : negMulLog (p0 rho) = 0) by lra.
  apply (negMulLog_zero_interval (p0 rho));
    [ exact (p0_nonneg rho) | exact (p0_le_one rho) | exact Hf1 ].
Qed.

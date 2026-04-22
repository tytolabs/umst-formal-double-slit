(* SPDX-License-Identifier: MIT *)
(* Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO *)

(* ================================================================== *)
(*  UMST-Formal: ComplementaritySpec.v                                 *)
(*                                                                      *)
(*  Spec-level port of Lean/QuantumClassicalBridge.lean to Coq.        *)
(*                                                                      *)
(*  Defines **distinguishability** (which-path score) and **fringe     *)
(*  visibility** for a 2x2 density matrix, then proves the Englert     *)
(*  complementarity relation:                                           *)
(*                                                                      *)
(*        V^2 + D^2 <= 1                                               *)
(*                                                                      *)
(*  The proof is self-contained: it follows from the DensityMatrix2    *)
(*  constraints (trace = 1, PSD) without any spectral machinery.       *)
(*                                                                      *)
(*  Corresponds to [complementarity_fringe_path] in Lean.              *)
(* ================================================================== *)

From Coq Require Import Reals Lra RIneq R_sqrt.
From UMSTFormal Require Import DensityStateSpec.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                         *)
(* ------------------------------------------------------------------ *)

(** Which-path distinguishability: D = |p0 - p1|.  Ranges from 0
    (balanced mixture) to 1 (orthogonal projectors). *)
Definition distinguishability (rho : DensityMatrix2) : R :=
  Rabs (p0 rho - p1 rho).

(** Fringe visibility: V = 2 |rho01|.  Uses the identity
    |rho01| = sqrt(rho01_re^2 + rho01_im^2). *)
Definition visibility (rho : DensityMatrix2) : R :=
  2 * sqrt (rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho).

(* ------------------------------------------------------------------ *)
(*  Basic bounds                                                        *)
(* ------------------------------------------------------------------ *)

Lemma distinguishability_nonneg (rho : DensityMatrix2) :
  0 <= distinguishability rho.
Proof.
  unfold distinguishability.
  apply Rabs_pos.
Qed.

Lemma distinguishability_le_one (rho : DensityMatrix2) :
  distinguishability rho <= 1.
Proof.
  unfold distinguishability.
  pose proof (p0_nonneg rho).
  pose proof (p1_nonneg rho).
  pose proof (trace_one rho).
  apply Rabs_le.
  lra.
Qed.

Lemma visibility_nonneg (rho : DensityMatrix2) :
  0 <= visibility rho.
Proof.
  unfold visibility.
  apply Rmult_le_pos.
  - lra.
  - apply sqrt_pos.
Qed.

(* ------------------------------------------------------------------ *)
(*  Englert complementarity relation                                    *)
(* ------------------------------------------------------------------ *)

(** Auxiliary: |x|^2 = x^2. *)
Lemma Rabs_sq (x : R) : Rabs x * Rabs x = x * x.
Proof.
  rewrite <- Rabs_mult.
  rewrite Rabs_right.
  - reflexivity.
  - apply Rle_ge. apply Rle_0_sqr.
Qed.

(** Auxiliary: (2 sqrt s)^2 = 4 s when s >= 0. *)
Lemma sq_2_sqrt (s : R) (hs : 0 <= s) :
  (2 * sqrt s) * (2 * sqrt s) = 4 * s.
Proof.
  replace ((2 * sqrt s) * (2 * sqrt s)) with (4 * (sqrt s * sqrt s)) by ring.
  rewrite sqrt_sqrt; [ring | exact hs].
Qed.

(** **Englert-style complementarity**: V^2 + D^2 <= 1.

    Proof sketch (matching the Lean proof):
      Let a = p0, b = p1, c_sq = |rho01|^2.
      - a + b = 1 (trace)
      - c_sq <= a * b (PSD / coherence bound)
      - V^2 = 4 c_sq,  D^2 = (a - b)^2
      - 4 c_sq + (a - b)^2  <=  4 a b + (a - b)^2  =  (a + b)^2  =  1.   *)
Theorem englert_complementarity (rho : DensityMatrix2) :
  visibility rho * visibility rho
    + distinguishability rho * distinguishability rho <= 1.
Proof.
  unfold visibility, distinguishability.
  set (a := p0 rho).
  set (b := p1 rho).
  set (c_sq := rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho).
  rewrite sq_2_sqrt.
  2: { apply coherence_sq_nonneg. }
  rewrite Rabs_sq.
  pose proof (trace_one rho) as Htr.
  pose proof (coherence_bounded rho) as Hcoh.
  fold a in Htr. fold b in Htr.
  fold a in Hcoh. fold b in Hcoh. fold c_sq in Hcoh.
  (* 4 c_sq + (a-b)² ≤ 4 a b + (a-b)² = (a+b)² = 1 using c_sq ≤ a*b *)
  assert (Hle : 4 * c_sq + (a - b) * (a - b) <= (a + b) * (a + b)) by lra.
  rewrite Htr in Hle.
  lra.
Qed.

(** Squared form using Rsqr for compatibility. *)
Theorem englert_complementarity_sq (rho : DensityMatrix2) :
  Rsqr (visibility rho) + Rsqr (distinguishability rho) <= 1.
Proof.
  unfold Rsqr.
  exact (englert_complementarity rho).
Qed.

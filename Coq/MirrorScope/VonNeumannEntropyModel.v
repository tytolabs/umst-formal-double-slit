(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* P0-13b: Shannon / spectral entropy assumptions as Records (no global Axiom). *)

From Coq Require Import Reals Lra RIneq Rpower.
From UMSTFormal Require Import DensityStateSpec VonNeumannEntropySpec.

Open Scope R_scope.

Record ShannonRealAnalysis : Set := {
  negMulLog_zero_interval_law :
    forall x : R, 0 <= x -> x <= 1 -> negMulLog x = 0 -> x = 0 \/ x = 1;
  shannon_binary_le_ln2_law :
    forall (p : R) (hp0 : 0 <= p) (hp1 : p <= 1),
      shannon_binary p <= ln 2
}.

Section WithShannonRealAnalysis.
  Variable S : ShannonRealAnalysis.

  Definition negMulLog_zero_interval :=
    negMulLog_zero_interval_law S.
  Definition shannon_binary_le_ln2 :=
    shannon_binary_le_ln2_law S.

  Lemma vonNeumannDiagonal_le_ln2_scoped (rho : DensityMatrix2) :
    vonNeumannDiagonal rho <= ln 2.
  Proof.
    unfold vonNeumannDiagonal.
    apply shannon_binary_le_ln2.
    - exact (p0_nonneg rho).
    - exact (p0_le_one rho).
  Qed.

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

End WithShannonRealAnalysis.

Record SpectralVonNeumannEntropy : Set := {
  vonNeumannEntropy_fn : DensityMatrix2 -> R;
  vonNeumannEntropy_nonneg_law :
    forall rho : DensityMatrix2, 0 <= vonNeumannEntropy_fn rho;
  vonNeumannEntropy_le_ln2_law :
    forall rho : DensityMatrix2, vonNeumannEntropy_fn rho <= ln 2;
  vonNeumannDiagonal_ge_spectral_law :
    forall rho : DensityMatrix2,
      vonNeumannDiagonal rho >= vonNeumannEntropy_fn rho;
  vonNeumannEntropy_unitary_invariant_law :
    forall (rho : DensityMatrix2) (U_det_one : True),
      vonNeumannEntropy_fn rho = vonNeumannEntropy_fn rho;
  vonNeumannEntropy_pure_zero_law :
    forall (rho : DensityMatrix2),
      p0 rho * p1 rho = rho01_re rho * rho01_re rho + rho01_im rho * rho01_im rho ->
      vonNeumannEntropy_fn rho = 0;
  vonNeumannEntropy_maximally_mixed_law :
    forall (rho : DensityMatrix2),
      p0 rho = 1/2 -> p1 rho = 1/2 ->
      rho01_re rho = 0 -> rho01_im rho = 0 ->
      vonNeumannEntropy_fn rho = ln 2
}.

Section WithSpectralEntropy.
  Variable E : SpectralVonNeumannEntropy.
  Definition vonNeumannEntropy := vonNeumannEntropy_fn E.
End WithSpectralEntropy.

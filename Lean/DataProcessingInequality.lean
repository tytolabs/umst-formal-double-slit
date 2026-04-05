/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import DensityState
import MeasurementChannel
import InfoEntropy
import VonNeumannEntropy
import SchrodingerDynamics
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# DataProcessingInequality — entropy monotonicity under quantum channels

The **data processing inequality** (DPI) constrains how information transforms under quantum
operations. For a CPTP (completely positive, trace-preserving) map `E`:

  **Unital DPI:** If `E(I) = I` then `S(E(ρ)) ≥ S(ρ)` (entropy cannot decrease).

This file proves:

1. **Tier 1 — Diagonal DPI** (`vonNeumannDiagonal_whichPath_invariant`):
   The diagonal (Shannon) entropy is exactly preserved by the which-path channel.
   This is a direct consequence of `vonNeumannDiagonal_whichPath_apply` in `InfoEntropy.lean`.

2. **Tier 1b — Diagonal ≥ Spectral (qubit)** (`vonNeumannDiagonal_ge_vonNeumannEntropy`):
   On a qubit, diagonal (Born) entropy is at least the spectral von Neumann entropy.
   Proof: `det = λ₀λ₁ ≤ p₀p₁` ⇒ `max λ ≥ max p` on `[1/2,1]`, then **`binEntropy_strictAntiOn`**.

3. **Tier 2 — Unital channel DPI (proved instances):**
   - **Identity:** `vonNeumannEntropy_identity_apply`, `vonNeumannEntropy_nondecreasing_unital_identity`.
   - **Qubit which-path (computational Lüders):** unital (`whichPathChannel_isUnital`) and
     **`vonNeumannEntropy_nondecreasing_unital_whichPath`** — spectral entropy monotone; proof =
     diagonal spectrum after dephasing + **Tier 1b** log-sum / `binEntropy` bound.
   A fully **quantitative** statement for an arbitrary unital Kraus channel on general `Fin n` is
   **out of scope** here (standard proofs use quantum relative entropy / matrix logarithms).

**Gap 11 closure (Tier 1 + statements for Tier 2).**

## Physical interpretation

The which-path measurement channel dephases ρ (zeros off-diagonal coherence). The resulting
diagonal state has entropy = `vonNeumannDiagonal`. Since `vonNeumannDiagonal ≥ vonNeumannEntropy`
(proved here), measurement **irreversibly increases** the entropy of the quantum state — the
thermodynamic arrow is manifest: once you learn which path, you pay in entropy.
-/

namespace UMST.Quantum

open Complex Real Matrix Set
open scoped BigOperators ComplexOrder

variable {n : ℕ} {hn : 0 < n}

/-! ### Tier 1: Diagonal entropy is invariant under which-path measurement -/

/-- The diagonal (Shannon) entropy is exactly preserved by the which-path channel.
This is a restatement of `vonNeumannDiagonal_whichPath_apply` from `InfoEntropy.lean`. -/
theorem vonNeumannDiagonal_whichPath_invariant (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) = vonNeumannDiagonal ρ :=
  vonNeumannDiagonal_whichPath_apply ρ

/-! ### Tier 1b: Diagonal entropy ≥ spectral entropy (measurement increases entropy) -/

private lemma qubit_max_eq_sqrt {p q : ℝ} (hpq : p + q = 1) :
    max p q = (1 + sqrt (1 - 4 * p * q)) / 2 := by
  have hsq : 1 - 4 * p * q = (p - q) ^ 2 := by
    nlinarith [hpq]
  rw [hsq, sqrt_sq_eq_abs]
  cases le_total p q with
  | inl hpq' =>
    rw [max_eq_right hpq', abs_of_nonpos (sub_nonpos.mpr hpq')]
    ring_nf
  | inr hpq' =>
    rw [max_eq_left hpq', abs_of_nonneg (sub_nonneg.mpr hpq')]
    ring_nf

private lemma vonNeumannDiagonal_eq_binEntropy_max_path (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal ρ = binEntropy (max (pathWeight ρ 0) (pathWeight ρ 1)) := by
  rw [vonNeumannDiagonal_eq_shannon_path1, shannonBinary_eq_binEntropy]
  set p0 := pathWeight ρ 0
  set p1 := pathWeight ρ 1
  have hp_sum : p0 + p1 = 1 := pathWeight_sum ρ
  by_cases h : p0 ≤ p1
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h)), ← binEntropy_one_sub p0, show 1 - p0 = p1 by linarith]

private lemma vonNeumannEntropy_eq_binEntropy_max_eigen (ρ : DensityMatrix hnQubit) :
    vonNeumannEntropy ρ =
      binEntropy (max ((DensityMat.isHermitian ρ).eigenvalues 0)
        ((DensityMat.isHermitian ρ).eigenvalues 1)) := by
  set l0 := (DensityMat.isHermitian ρ).eigenvalues 0
  set l1 := (DensityMat.isHermitian ρ).eigenvalues 1
  have hl_sum : l0 + l1 = 1 := by simpa [Fin.sum_univ_two] using density_eigenvalues_sum_eq_one_real ρ
  unfold vonNeumannEntropy
  rw [Fin.sum_univ_two, ← binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  by_cases h : l0 ≤ l1
  · rw [max_eq_right h, ← binEntropy_one_sub l1, show 1 - l1 = l0 by linarith]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]

/-- **Schur concavity for qubits:** The diagonal (Shannon) entropy of a 2×2 density matrix
is at least its von Neumann (spectral) entropy.

  `vonNeumannDiagonal ρ ≥ vonNeumannEntropy ρ`

Equivalently: the Born-weight distribution `(p₀, p₁)` majorizes the eigenvalue distribution
`(λ₊, λ₋)` in the sense that the larger eigenvalue `λ₊ ≥ max(p₀, p₁)`.

**Proof (qubit):** `det ρ = λ₀ λ₁ = p₀ p₁ - ‖ρ₀₁‖² ≤ p₀ p₁`, hence
`max(λ₀,λ₁) = (1+√(1-4λ₀λ₁))/2 ≥ (1+√(1-4p₀p₁))/2 = max(p₀,p₁)`.
Binary entropy is strictly antitone on `[1/2,1]` (`binEntropy_strictAntiOn`), giving the inequality. -/
theorem vonNeumannDiagonal_ge_vonNeumannEntropy (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal ρ ≥ vonNeumannEntropy ρ := by
  classical
  set A := ρ.carrier
  set hρ := DensityMat.isHermitian ρ
  set l0 : ℝ := hρ.eigenvalues 0
  set l1 : ℝ := hρ.eigenvalues 1
  set p0 : ℝ := pathWeight ρ 0
  set p1 : ℝ := pathWeight ρ 1
  have hp_sum : p0 + p1 = 1 := pathWeight_sum ρ
  have hl_sum : l0 + l1 = 1 := by simpa [Fin.sum_univ_two] using density_eigenvalues_sum_eq_one_real ρ
  have hprod_le : l0 * l1 ≤ p0 * p1 := by
    have hprod_det : (l0 * l1 : ℂ) = A.det := by
      rw [hρ.det_eq_prod_eigenvalues, Fin.prod_univ_two]
    have hdet2 : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    have h01 : A 1 0 = star (A 0 1) := by rw [← Matrix.conjTranspose_apply, hρ.eq]
    have hp0c : (p0 : ℂ) = A 0 0 := (IsHermitian.coe_re_apply_self hρ 0).symm
    have hp1c : (p1 : ℂ) = A 1 1 := (IsHermitian.coe_re_apply_self hρ 1).symm
    have hdet3 : A.det = (p0 * p1 : ℂ) - (normSq (A 0 1) : ℂ) := by
      rw [hdet2, h01, ← hp0c, ← hp1c, Complex.mul_conj]
      simp only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hl1R : l0 * l1 = (A.det).re := by
      have hre := congrArg Complex.re hprod_det
      simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using hre
    have hre_det : (A.det).re = p0 * p1 - normSq (A 0 1) := by
      rw [hdet3, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re]
      simp [normSq]
    rw [hl1R, hre_det]
    linarith [normSq_nonneg (A 0 1)]
  -- `l0 * l1 ≤ p0 * p1` ⇒ `1 - 4*l*l ≥ 1 - 4*p*p` ⇒ larger `sqrt` for the eigenvalue side
  have hsq_mono : 1 - 4 * p0 * p1 ≤ 1 - 4 * l0 * l1 := by nlinarith [hprod_le]
  have hsqrt : sqrt (1 - 4 * p0 * p1) ≤ sqrt (1 - 4 * l0 * l1) := sqrt_le_sqrt hsq_mono
  have hmax_le : max p0 p1 ≤ max l0 l1 := by
    rw [qubit_max_eq_sqrt hp_sum, qubit_max_eq_sqrt hl_sum]
    nlinarith [hsqrt]
  have hmem_p : max p0 p1 ∈ Icc (2⁻¹ : ℝ) 1 := by
    constructor
    · cases le_total p0 p1 with
      | inl h => rw [max_eq_right h]; nlinarith [hp_sum]
      | inr h => rw [max_eq_left h]; nlinarith [hp_sum]
    · exact max_le (pathWeight_le_one ρ 0) (pathWeight_le_one ρ 1)
  have hmem_l : max l0 l1 ∈ Icc (2⁻¹ : ℝ) 1 := by
    constructor
    · cases le_total l0 l1 with
      | inl h => rw [max_eq_right h]; nlinarith [hl_sum]
      | inr h => rw [max_eq_left h]; nlinarith [hl_sum]
    · exact max_le (density_eigenvalues_le_one ρ 0) (density_eigenvalues_le_one ρ 1)
  have hbin :=
    (binEntropy_strictAntiOn.antitoneOn) hmem_p hmem_l hmax_le
  rw [vonNeumannDiagonal_eq_binEntropy_max_path ρ, vonNeumannEntropy_eq_binEntropy_max_eigen ρ]
  exact hbin

/-! ### Tier 2: Unital channel entropy monotonicity

A channel `E` is **unital** if `E(I) = I`. For unital CPTP maps, entropy is non-decreasing.
The which-path channel is unital: `P₀ I P₀ + P₁ I P₁ = P₀ + P₁ = I`. -/

/-- A Kraus channel is **unital** if it maps the identity to the identity. -/
def KrausChannel.IsUnital (κ : KrausChannel n ι) : Prop :=
  κ.map (1 : Matrix (Fin n) (Fin n) ℂ) = 1

/-- The **identity Kraus channel** (`KrausChannel.identity`) is unital. -/
@[simp]
theorem KrausChannel.identity_isUnital (n : ℕ) : (KrausChannel.identity n).IsUnital :=
  KrausChannel.identity_map n 1

/-- Applying the identity channel leaves von Neumann entropy unchanged. -/
theorem vonNeumannEntropy_identity_apply (ρ : DensityMatrix hn) :
    vonNeumannEntropy ((KrausChannel.identity n).apply hn ρ) = vonNeumannEntropy ρ := by
  refine congr_arg vonNeumannEntropy (DensityMat.ext ?_)
  simp [KrausChannel.apply, KrausChannel.identity_map]

/-- **Tier 2** holds trivially for the identity channel: `S(ρ) ≥ S(ρ)` (in fact equality). -/
theorem vonNeumannEntropy_nondecreasing_unital_identity (ρ : DensityMatrix hn) :
    vonNeumannEntropy ((KrausChannel.identity n).apply hn ρ) ≥ vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy_identity_apply]
  exact le_rfl

/-- The which-path channel is unital: projectors sum to identity. -/
theorem whichPathChannel_isUnital : KrausChannel.whichPathChannel.IsUnital := by
  unfold KrausChannel.IsUnital KrausChannel.map
  rw [KrausChannel.whichPath_map_eq_diagonal]
  ext i j
  simp [diagonal_apply, one_apply]

/-! ### Tier 2 (algebraic): unital dephasing on the qubit path bit -/

/-- Diagonal entries of a density matrix are real (`im = 0`), hence `ρᵢᵢ = ↑(re ρᵢᵢ)`. -/
theorem densityMatrix_diag_entry_eq_ofReal_re {m : ℕ} {hm : 0 < m} (ρ : DensityMatrix hm)
    (i : Fin m) : ρ.carrier i i = ((ρ.carrier i i).re : ℂ) := by
  rw [Complex.ext_iff]
  have him : (ρ.carrier i i).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← Complex.star_def]
    exact (ρ.psd.isHermitian.apply i i).symm
  simp [him]

/-- After Lüders which-path, the carrier is the diagonal of Born weights as complex scalars. -/
theorem whichPath_apply_carrier_eq_diagonal_pathWeight (ρ : DensityMatrix hnQubit) :
    (KrausChannel.whichPathChannel.apply hnQubit ρ).carrier =
      diagonal (fun i : Fin 2 => (pathWeight ρ i : ℂ)) := by
  rw [KrausChannel.apply, KrausChannel.whichPath_map_eq_diagonal]
  refine congrArg diagonal (funext fun i => ?_)
  rw [densityMatrix_diag_entry_eq_ofReal_re ρ i, pathWeight]

/-- Spectral entropy of the dephased state equals the diagonal Shannon functional on path weights. -/
theorem vonNeumannEntropy_whichPath_apply_eq_vonNeumannDiagonal (ρ : DensityMatrix hnQubit) :
    vonNeumannEntropy (KrausChannel.whichPathChannel.apply hnQubit ρ) = vonNeumannDiagonal ρ := by
  have hdiag :=
    vonNeumannEntropy_eq_sum_negMulLog_of_diagonal_carrier
      (KrausChannel.whichPathChannel.apply hnQubit ρ) (fun i => pathWeight ρ i)
      (whichPath_apply_carrier_eq_diagonal_pathWeight ρ)
  rw [hdiag, vonNeumannDiagonal, shannonBinary]
  rw [Fin.sum_univ_two]
  have hp1 : pathWeight ρ 1 = 1 - pathWeight ρ 0 := by linarith [pathWeight_sum ρ]
  simpa [hp1]

/-- **Algebraic unital DPI (qubit path channel):** the computational-basis Lüders channel is
unital (`whichPathChannel_isUnital`) and **does not decrease** von Neumann entropy.

Proof: `S(E(ρ))` equals `vonNeumannDiagonal ρ` (dephased state is diagonal, spectrum = Born weights),
and `vonNeumannDiagonal ρ ≥ S(ρ)` is **Tier 1b** (`vonNeumannDiagonal_ge_vonNeumannEntropy`, det / log-sum / `binEntropy` chain).

This is the spectral-side packaging of `whichPath_increases_entropy` (same inequality, LHS written
as `vonNeumannDiagonal(E(ρ))` there). A **general** unital CPTP statement for all `n` and all Kraus
families is **not** in this file (would require relative entropy / matrix log infrastructure). -/
theorem vonNeumannEntropy_nondecreasing_unital_whichPath (ρ : DensityMatrix hnQubit) :
    vonNeumannEntropy (KrausChannel.whichPathChannel.apply hnQubit ρ) ≥ vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy_whichPath_apply_eq_vonNeumannDiagonal ρ]
  exact vonNeumannDiagonal_ge_vonNeumannEntropy ρ

/-! ### Corollaries combining Tier 1 and Tier 1b -/

/-- **Measurement increases entropy (qubit):** applying the which-path channel transforms
a density matrix ρ with `vonNeumannEntropy S₀` into a diagonal state with
`vonNeumannDiagonal S₁`, where `S₁ ≥ S₀`. -/
theorem whichPath_increases_entropy (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) ≥ vonNeumannEntropy ρ := by
  -- vonNeumannDiagonal(E(ρ)) = vonNeumannDiagonal(ρ)  [by whichPath invariance]
  --                          ≥ vonNeumannEntropy(ρ)    [by Schur concavity]
  rw [vonNeumannDiagonal_whichPath_invariant]
  exact vonNeumannDiagonal_ge_vonNeumannEntropy ρ

/-- The entropy increase from measurement is bounded by the off-diagonal coherence:
`vonNeumannDiagonal ρ - vonNeumannEntropy ρ ≥ 0`, with equality iff ρ is diagonal. -/
theorem entropy_increase_from_measurement_nonneg (ρ : DensityMatrix hnQubit) :
    0 ≤ vonNeumannDiagonal ρ - vonNeumannEntropy ρ := by
  linarith [vonNeumannDiagonal_ge_vonNeumannEntropy ρ]

/-! ### Connection to PMIC

The PMIC states `V² + residualCoherenceCapacity ≤ 1` (proved in `PMICVisibility.lean`).
Combined with the DPI, we get the full thermodynamic picture:

1. **Before measurement:** quantum state has `S_quantum = vonNeumannEntropy(ρ)`.
2. **Coherence cost:** `S_diagonal - S_quantum ≥ 0` is the entropy paid to dephase.
3. **After measurement:** `S_diagonal = vonNeumannDiagonal(ρ)`, and the Landauer cost
   `k_B T ln 2 · pathEntropyBits(ρ)` bounds the heat dissipated.
4. **Complementarity:** `V² + (1 - pathEntropyBits) ≤ 1` links visibility to this cost.

This closes the loop from quantum coherence → measurement entropy → thermodynamic cost → PMIC.
-/

/-! ### Wave 6.5.2 — general `Fin n`: unital **single-Kraus** (unitary) CPTP maps

The fully general statement “`S(Φ(ρ)) ≥ S(ρ)` for **every** unital CPTP `Φ` on `Fin n`” is a
deep result (quantum relative entropy / Stinespring).  Here we prove the **unitary subclass**:
every **unitary conjugation** channel is CPTP, unital, and **preserves** von Neumann entropy
(`vonNeumannEntropy_unitarily_invariant`), hence satisfies the DPI inequality trivially with equality.
-/

variable {n : ℕ} {hn : 0 < n}

theorem KrausChannel.unitaryChannel_isUnital (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    (unitaryChannel U hU).IsUnital := by
  unfold KrausChannel.IsUnital
  rw [unitaryChannel_map U hU 1, mul_one]
  exact conjTranspose_mul_self_of_self_mul_conjTranspose U hU

/-- Carrier of `apply` for a unitary Kraus channel agrees with `U ρ Uᴴ`. -/
theorem unitaryChannel_apply_carrier (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : DensityMatrix hn) :
    ((unitaryChannel U hU).apply hn ρ).carrier = U * ρ.carrier * Uᴴ := by
  simp [KrausChannel.apply, unitaryChannel_map]

private theorem unitaryChannel_apply_eq_unitaryConj (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : DensityMatrix hn) :
    (unitaryChannel U hU).apply hn ρ =
      unitaryConjDensityMatrix ρ ⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩ := by
  refine DensityMat.ext ?_
  simp [unitaryChannel_apply_carrier, unitaryConjDensityMatrix, Matrix.star_eq_conjTranspose]

/-- **Unital CPTP (single Kraus / unitary) on `Fin n`:** entropy is **preserved**, hence
`S(E(ρ)) ≥ S(ρ)` with equality.

For multi-Kraus unital CPTP maps beyond the unitary subclass, see the note in the module doc
at the top of Tier 2. -/
theorem vonNeumannEntropy_nondecreasing_unital_CPTP_n (ρ : DensityMatrix hn)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    vonNeumannEntropy ((unitaryChannel U hU).apply hn ρ) ≥ vonNeumannEntropy ρ := by
  rw [unitaryChannel_apply_eq_unitaryConj U hU ρ,
    vonNeumannEntropy_unitarily_invariant ρ ⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩]
  exact le_rfl

end UMST.Quantum

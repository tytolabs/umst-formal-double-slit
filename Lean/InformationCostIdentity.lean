/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import LandauerBound
import EpistemicMI

/-!
# InformationCostIdentity — residual coherence vs extracted mutual information

Connects:

- `residualCoherenceCapacity ρ = 1 - pathEntropyBits ρ` (`LandauerBound`)
- `epistemicMIBits PathProbe.whichPath ρ = pathEntropyBits ρ` (`EpistemicMI`)

**Prompt ratio (dimensionless).** With epistemic MI in **nats**, the Landauer **energy per bit**
is `k_B T ln 2 = landauerBitEnergy T` (joules).  The dimensionless **bit-equivalent** extracted
information is `MI / ln 2`.  On the one-bit path-qubit hook, `residual = 1 - MI/ln 2`, i.e.
`1 - MI_bit`.  Equivalently, if one records **Landauer-equivalent energy** `Q ≥ MI_bit · k_B T ln 2`,
then `MI_bit ≤ Q / (k_B T ln 2)` and `1 - Q/(k_B T ln 2) ≤ residual` when the inequalities bind
along the same calibration (see `landauer_ratio_le_one_minus_residual`).

Thermodynamic cost `Q` is bounded below by `infoEnergyLowerBound` in joules.

**Deception / suppression:** extracting *more* path information (larger epistemic MI bits)
**increases** the Landauer lower bound and **decreases** residual coherence (antitone in bits).
-/

namespace UMST.AgentDynamics

open UMST.Core UMST.Quantum UMST.DoubleSlit Real

/-- Dimensionless residual from extracted MI in **Landauer bit-equivalents** (`MI_nats / ln 2`). -/
noncomputable def residualCoherenceFromMIBits (miBits : ℝ) : ℝ :=
  1 - miBits

theorem residualCoherence_eq_one_minus_epistemic_bits (ρ : DensityMatrix hnQubit) :
    residualCoherenceFromMIBits (epistemicMIBits PathProbe.whichPath ρ) =
      residualCoherenceCapacity ρ := by
  unfold residualCoherenceFromMIBits residualCoherenceCapacity
  rw [epistemicMIBits_whichPath]

lemma landauerBitEnergy_pos {T : ℝ} (hT : 0 < T) : 0 < landauerBitEnergy T := by
  unfold landauerBitEnergy
  exact mul_pos (mul_pos kB_pos hT) (log_pos (by norm_num : (1 : ℝ) < 2))

/-- Energy lower bound (joules) equals `MI_bit · k_B T ln 2` on this hook. -/
theorem epistemic_landauer_as_bit_times_scale (ρ : DensityMatrix hnQubit) (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath ρ T =
      landauerBitEnergy T * epistemicMIBits PathProbe.whichPath ρ := by
  unfold epistemicLandauerCost epistemicMIBits infoEnergyLowerBound
  ring

/-- Monotone lower bound on dissipation scale in `T` with fixed extracted bits: larger `b` ⇒ larger `Q_lower`. -/
theorem infoEnergyLowerBound_monotone_bits (b₁ b₂ T : ℝ) (_hb₁ : 0 ≤ b₁) (hle : b₁ ≤ b₂)
    (hT : 0 ≤ T) :
    infoEnergyLowerBound b₁ T ≤ infoEnergyLowerBound b₂ T := by
  unfold infoEnergyLowerBound
  exact mul_le_mul_of_nonneg_left hle (landauerBitEnergy_nonneg hT)

/-- **Deception / stronger extraction:** if an observer realizes **at least** as many epistemic
bit-equivalents as another configuration, the Landauer lower bound is no smaller. -/
theorem epistemic_landauer_monotone_in_probe_bits (p q : PathProbe) (ρ σ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) (hbits : epistemicMIBits p ρ ≤ epistemicMIBits q σ) :
    epistemicLandauerCost p ρ T ≤ epistemicLandauerCost q σ T := by
  unfold epistemicLandauerCost
  exact infoEnergyLowerBound_monotone_bits _ _ T (epistemicMIBits_nonneg p ρ) hbits hT

/-- If realized dissipation `Q` is at least the Landauer lower bound, then
`Q / (k_B T ln 2) ≥ MI_bit` and `1 - Q/(k_B T ln 2) ≤ residual` (one-bit bookkeeping). -/
theorem landauer_ratio_le_one_minus_residual (ρ : DensityMatrix hnQubit) (T : ℝ) (Q : ℝ)
    (hT : 0 < T) (hQ : epistemicLandauerCost PathProbe.whichPath ρ T ≤ Q) :
    epistemicMIBits PathProbe.whichPath ρ ≤ Q / landauerBitEnergy T := by
  have hden : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  rw [epistemic_landauer_as_bit_times_scale ρ T] at hQ
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hQ)

theorem one_minus_ratio_le_residualCoherence (ρ : DensityMatrix hnQubit) (T : ℝ) (Q : ℝ)
    (hT : 0 < T) (hQ : epistemicLandauerCost PathProbe.whichPath ρ T ≤ Q) :
    1 - Q / landauerBitEnergy T ≤ residualCoherenceCapacity ρ := by
  have hres := residualCoherence_eq_one_minus_epistemic_bits ρ
  rw [← hres]
  unfold residualCoherenceFromMIBits
  linarith [landauer_ratio_le_one_minus_residual ρ T Q hT hQ]

/-- Residual coherence is **antitone** in extracted path bits: more which-path information ⇒
smaller `1 - bits`. -/
theorem residual_antitone_in_path_bits (b₁ b₂ : ℝ) (hle : b₁ ≤ b₂) :
    1 - b₂ ≤ 1 - b₁ := by
  linarith

theorem residualCoherence_antitone_pathEntropyBits (ρ σ : DensityMatrix hnQubit)
    (hle : pathEntropyBits ρ ≤ pathEntropyBits σ) :
    residualCoherenceCapacity σ ≤ residualCoherenceCapacity ρ := by
  unfold residualCoherenceCapacity
  exact residual_antitone_in_path_bits _ _ hle

end UMST.AgentDynamics

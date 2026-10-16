-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal-Double-Slit: Learning/EvidenceCost.lean

  A verification of a close is an observation: it reads the close into a record, and the record's evidence bits are
  paid for when the record is reset. Stated through the one predicate `UMST.ProcessFamily.SecondLaw` of umst-formal,
  with no law of its own:

  * erasing a record of `b` evidence bits (the uniform distribution on `2^b` states to a point) under the erase case
    costs at least `b · k_B T ln 2` (`evidenceBits_cost_ge`, through `CostOfInformation.bitErasure_cost`), so the
    evidence bits per joule of a verification are at most `1 / (k_B T ln 2)` (`evidenceBitsPerJoule_le`);
  * on the knowing fibre's path qubit, a verification whose record is the path record pays for its path-entropy bits
    at the same rate (`pathEvidencePerJoule_le`, through `KnowingFibreLaw.erase_pathRecord_cost_ge_bits`), and its
    reset costs at least the larger of the Landauer bound on its bits and the Englert bound `k_B T V² / 2` on the
    fringes it erases (`pathEvidence_cost_ge_max`).

  Zero `axiom`, zero `sorry`.
-/

import KnowingFibreLaw
import CostOfInformation

open Real UMST.LandauerLaw UMST.ProcessFamily UMST.DoubleSlit UMST.DoubleSlit.KnowingFibreLaw
open UMST.Quantum UMST.DoubleSlit.KnowingFibreInstance

namespace UMST.DoubleSlit.Learning

/-- The Landauer bit energy at a positive temperature is positive. -/
theorem landauerBitEnergy_pos' {T : ℝ} (hT : 0 < T) : 0 < landauerBitEnergy T := by
  rw [landauerBitEnergy_eq_kB]
  exact mul_pos (mul_pos kB_pos hT) (Real.log_pos (by norm_num))

/-- **Each evidence bit costs at least `k_B T ln 2`.** A verification whose record of `b` evidence bits is reset by
    an erasure obeying the erase case pays at least `b · k_B T ln 2` joules. -/
theorem evidenceBits_cost_ge (b : HeatBath) (W : ℝ) (bits : ℕ)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    (bits : ℝ) * landauerBitEnergy b.bathTemp.val ≤ kB * W := by
  have hc := UMST.CostOfInformation.bitErasure_cost b W bits h
  rw [landauerBitEnergy_eq_kB]
  exact hc

/-- **Evidence per joule is bounded.** With a positive reset work, the evidence bits per joule are at most
    `1 / (k_B T ln 2)`. -/
theorem evidenceBitsPerJoule_le (b : HeatBath) (W : ℝ) (hW : 0 < W) (bits : ℕ)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    (bits : ℝ) / (kB * W) ≤ 1 / landauerBitEnergy b.bathTemp.val := by
  have hL := landauerBitEnergy_pos' b.bathTemp.property
  have hkW : 0 < kB * W := mul_pos kB_pos hW
  rw [div_le_div_iff₀ hkW hL, one_mul]
  have := evidenceBits_cost_ge b W bits h
  linarith

/-- **On the path qubit.** A verification whose record is the path record, reset with positive work under the erase
    case, extracts at most `1 / (k_B T ln 2)` path-entropy bits per joule. -/
theorem pathEvidencePerJoule_le (e : UMST.LandauerLaw.ErasureProcess) (ρ : UMST.Quantum.DensityMatrix UMST.Quantum.hnQubit)
    (hW : 0 < e.work) (h : SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    pathEntropyBits ρ / (kB * e.work) ≤ 1 / landauerBitEnergy e.bath.bathTemp.val := by
  have hL := landauerBitEnergy_pos' e.bath.bathTemp.property
  have hkW : 0 < kB * e.work := mul_pos kB_pos hW
  rw [div_le_div_iff₀ hkW hL, one_mul]
  have := erase_pathRecord_cost_ge_bits e ρ h
  linarith

/-- **Landauer and Englert together.** Resetting the path record costs at least the larger of the Landauer bound on
    its evidence bits and the Englert bound `k_B T V² / 2` on the fringes it erases. -/
theorem pathEvidence_cost_ge_max (e : UMST.LandauerLaw.ErasureProcess) (ρ : UMST.Quantum.DensityMatrix UMST.Quantum.hnQubit)
    (h : SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    max (landauerBitEnergy e.bath.bathTemp.val * pathEntropyBits ρ)
        (kB * e.bath.bathTemp.val * fringeVisibility ρ ^ 2 / 2) ≤ kB * e.work :=
  max_le (erase_pathRecord_cost_ge_bits e ρ h) (erase_pathRecord_cost_ge_visibility_sq e ρ h)

end UMST.DoubleSlit.Learning

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.Basic

/-!
# DensityState — finite-dimensional density matrices (minimal layer)

`n × n` complex matrices that are **positive semidefinite** and have **trace 1**, matching the
standard quantum density-operator interface.

**In this file:**
- `DensityMatrix hn` — public `abbrev` for **`DensityMatCore hn`** (bundled PSD + `trace = 1`).
- Lemmas in namespace **`DensityMat`** (e.g. **`DensityMat.ext`**, **`DensityMat.trace_eq_one`**) — avoids Lean path clashes between structure and lemma namespaces.
- `pureDensity ψ h` — rank-one projector `|ψ⟩⟨ψ|` from a normalized vector (`dotProduct ψ (star ψ) = 1`).

**In file:** convex **mixed state** `mixedDensity ρ₁ ρ₂ t` for `t ∈ [0,1]` (`PosSemidef.add` / `smul_psd`).

**Not yet:** general finite mixtures `∑ tᵢ ρᵢ`, or a dedicated bridge import from `DoubleSlitCore`.
**Composite / partial trace:** see **`TensorPartialTrace.lean`** (`tensorDensity`, `partialTraceRightProd`).
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

variable {n : ℕ} {hn : 0 < n}

local notation "ℂⁿ" => Fin n → ℂ

/-- Record name is disjoint from `namespace DensityMat` (lemmas), avoiding `UMST.Quantum.DensityMat`
path collision between structure and namespace. -/
structure DensityMatCore (hn : 0 < n) : Type where
  carrier : Matrix (Fin n) (Fin n) ℂ
  psd : carrier.PosSemidef
  trace_one : Matrix.trace carrier = 1

abbrev DensityMatrix (hn : 0 < n) : Type := DensityMatCore hn

/-- Enables `ρ.isHermitian` on `DensityMatrix` / `DensityMatCore` (carrier is Hermitian). -/
def DensityMatCore.isHermitian {hn : 0 < n} (ρ : DensityMatCore hn) : ρ.carrier.IsHermitian :=
  ρ.psd.isHermitian

namespace DensityMat

/-- Two density matrices are equal if their underlying matrices agree (PSD / trace proofs are
propositions, hence unique). -/
@[ext]
theorem ext {ρ σ : DensityMatCore hn} (h : ρ.carrier = σ.carrier) : ρ = σ := by
  rcases ρ with ⟨c, hp, ht⟩
  rcases σ with ⟨c', hp', ht'⟩
  subst h
  rfl

@[simp]
theorem trace_eq_one (ρ : DensityMatCore hn) : Matrix.trace ρ.carrier = 1 :=
  ρ.trace_one

theorem isHermitian (ρ : DensityMatCore hn) : ρ.carrier.IsHermitian :=
  ρ.psd.isHermitian

theorem diag_nonneg_complex_n (ρ : DensityMatCore hn) (i : Fin n) :
    (0 : ℂ) ≤ ρ.carrier i i := by
  have h := ρ.psd.2 (Pi.single i (1 : ℂ))
  have key : dotProduct (star (Pi.single i (1 : ℂ))) (ρ.carrier *ᵥ Pi.single i (1 : ℂ)) = ρ.carrier i i := by
    dsimp [dotProduct, mulVec]
    have inner (j : Fin n) : (∑ k : Fin n, ρ.carrier j k * ((Pi.single i (1:ℂ) : Fin n → ℂ) k)) = ρ.carrier j i := by
      rw [Finset.sum_eq_single i]
      · have hp : (Pi.single i (1:ℂ) : Fin n → ℂ) i = 1 := Pi.single_eq_same (f := fun _ => ℂ) i (1:ℂ)
        rw [hp, mul_one]
      · intro k _ hneq
        have hz : (Pi.single i (1:ℂ) : Fin n → ℂ) k = 0 := Pi.single_eq_of_ne (f := fun _ => ℂ) hneq (1:ℂ)
        rw [hz, mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    simp_rw [inner]
    rw [Finset.sum_eq_single i]
    · have hp : (Pi.single i (1:ℂ) : Fin n → ℂ) i = 1 := Pi.single_eq_same (f := fun _ => ℂ) i (1:ℂ)
      simp [hp]
    · intro j _ hneq
      have hzz : (Pi.single i (1:ℂ) : Fin n → ℂ) j = 0 := Pi.single_eq_of_ne (f := fun _ => ℂ) hneq (1:ℂ)
      simp [hzz]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rwa [key] at h

theorem diag_re_nonneg_n (ρ : DensityMatCore hn) (i : Fin n) :
    0 ≤ (ρ.carrier i i).re :=
  (Complex.nonneg_iff.mp (diag_nonneg_complex_n ρ i)).1

theorem trace_sum_s (S : Finset (Fin n)) (s : Fin n → ℂ) :
    Complex.re (∑ i in S, s i) = ∑ i in S, (s i).re := by
  induction S using Finset.induction
  case empty => simp
  case insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    simp [ih]

theorem trace_re_eq_one_n (ρ : DensityMatCore hn) :
    ∑ i : Fin n, (ρ.carrier i i).re = 1 := by
  have h := ρ.trace_one
  unfold Matrix.trace at h
  apply_fun Complex.re at h
  have hc : Complex.re (∑ i : Fin n, ρ.carrier.diag i) = ∑ i : Fin n, (ρ.carrier i i).re := by
    exact trace_sum_s Finset.univ (fun i => ρ.carrier i i)
  rw [hc] at h
  simp only [Complex.one_re] at h
  exact h

theorem diag_re_le_one_n (ρ : DensityMatCore hn) (i : Fin n) :
    (ρ.carrier i i).re ≤ 1 := by
  have hsum := trace_re_eq_one_n ρ
  have hrest : ∑ j in Finset.univ.erase i, (ρ.carrier j j).re ≥ 0 :=
    Finset.sum_nonneg (fun j _ => diag_re_nonneg_n ρ j)
  have heq : (ρ.carrier i i).re + ∑ j in Finset.univ.erase i, (ρ.carrier j j).re = 1 := by
    have h1 : ∑ j in Finset.univ, (ρ.carrier j j).re = 1 := hsum
    exact Eq.symm (Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun j => (ρ.carrier j j).re) (Finset.mem_univ i) ▸ Eq.symm h1)
  linarith

theorem smul_psd {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (r : ℝ) (hr : 0 ≤ r) :
    ((r : ℂ) • M).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.smul_apply, Matrix.conjTranspose_apply, star_smul]
    have h1 : M i j = star (M j i) := by exact (congrFun (congrFun hM.1.symm i) j)
    have hr_conj : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    rw [hr_conj, h1]
  · intro x
    have h1 := hM.2 x
    have step1 : Matrix.dotProduct (star x) (((r : ℂ) • M) *ᵥ x) = (r : ℂ) * Matrix.dotProduct (star x) (M *ᵥ x) := by
      dsimp [Matrix.dotProduct, Matrix.mulVec, Matrix.smul_apply, Pi.smul_apply]
      calc
        (∑ i : Fin n, star (x i) * ∑ j : Fin n, ((r : ℂ) * M i j) * x j)
          = ∑ i : Fin n, star (x i) * ∑ j : Fin n, (r : ℂ) * (M i j * x j) := by
            apply Finset.sum_congr rfl; intro i _; congr 1; apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ i : Fin n, star (x i) * ((r : ℂ) * ∑ j : Fin n, M i j * x j) := by
            apply Finset.sum_congr rfl; intro i _; congr 1; exact Eq.symm (Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun j => M i j * x j) (r : ℂ))
        _ = ∑ i : Fin n, (r : ℂ) * (star (x i) * ∑ j : Fin n, M i j * x j) := by
            apply Finset.sum_congr rfl; intro i _; ring
        _ = (r : ℂ) * ∑ i : Fin n, star (x i) * ∑ j : Fin n, M i j * x j := by
            exact Eq.symm (Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun i => star (x i) * ∑ j : Fin n, M i j * x j) (r : ℂ))
    rw [step1]
    exact mul_nonneg (Complex.zero_le_real.mpr hr) h1

/-- Convex combination of two density matrices: `t ρ₁ + (1 - t) ρ₂` for `0 ≤ t ≤ 1`. -/
noncomputable def mixedDensity (ρ₁ ρ₂ : DensityMatCore hn) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    DensityMatCore hn where
  carrier := (t : ℂ) • ρ₁.carrier + ((1 - t : ℝ) : ℂ) • ρ₂.carrier
  psd := by
    apply Matrix.PosSemidef.add
    · exact smul_psd ρ₁.psd t ht0
    · exact smul_psd ρ₂.psd (1 - t) (sub_nonneg.mpr ht1)
  trace_one := by
    dsimp
    simp only [Matrix.trace_smul, Matrix.trace_add]
    rw [trace_eq_one ρ₁, trace_eq_one ρ₂]
    simp [mul_one]

end DensityMat

open Matrix

/-- Rank-one projector `col ψ * row (star ψ)` (i.e. `|ψ⟩⟨ψ|` in bra-ket notation). -/
noncomputable def pureCarrier (ψ : ℂⁿ) : Matrix (Fin n) (Fin n) ℂ :=
  col Unit ψ * row Unit (star ψ)

theorem pureCarrier_posSemidef (ψ : ℂⁿ) : (pureCarrier ψ).PosSemidef := by
  simpa [pureCarrier] using posSemidef_self_mul_conjTranspose (col Unit ψ)

theorem pureCarrier_trace (ψ : ℂⁿ) :
    Matrix.trace (pureCarrier ψ) = dotProduct ψ (star ψ) := by
  simpa [pureCarrier] using trace_col_mul_row (ι := Unit) ψ (star ψ)

/-- Pure state from a vector normalized in the `dotProduct ψ (star ψ) = 1` convention. -/
noncomputable def pureDensity (ψ : ℂⁿ) (hψ : dotProduct ψ (star ψ) = 1) : DensityMatCore hn where
  carrier := pureCarrier ψ
  psd := pureCarrier_posSemidef ψ
  trace_one := by rw [pureCarrier_trace, hψ]

@[simp]
theorem pureDensity_carrier (ψ : ℂⁿ) (hψ : dotProduct ψ (star ψ) = 1) :
    (pureDensity (hn := hn) ψ hψ).carrier = pureCarrier ψ :=
  rfl

end UMST.Quantum
